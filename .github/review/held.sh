# shellcheck shell=bash
# held.sh: the functions and values of the rescreen pass. Two steps source this file, each at one place of its script:
# - the step "Start the runs that the open items are due" of .github/workflows/rescreen.yml, the rescreen pass;
# - the trust job's step "Whether the author and the account that started the run have write access" of
#   .github/workflows/review.yml. With these functions, the trust job of each run that the pass starts reads again why
#   the pass started it.
# Before that step, each of the two jobs checks out this file alone, at the commit whose workflow file runs (github.sha,
# a commit of main). So the file of that commit runs, and never a file of a pull request.
# Before the source line, each step sets seen, a directory that the step makes for itself, and defines the function
# trusted. After it, each step defines restart, which rerun calls. The functions and jq filters of the file read REPO,
# HELD_LABEL, REVIEW_TRIES and IMPORT_PATHS from the environment of the step, and RUN_ID, which the trust step alone
# sets. The source line sets values, defines functions, and makes $seen/due and $seen/stops empty. It reads nothing
# from GitHub.
# In the comments below, "this step" is the step that sources the file, and "this workflow" is review.yml.

# titled: the names of the runs that the rescreen pass starts and that name an account (run-name):
# <task> #<n>[ at <head>][ for <comment>] of <login>. BASH_REMATCH[2] is then the number, and [5] the login.
titled='^(rescreen|review|answer|draft|approve) #([1-9][0-9]*)( at [0-9a-f]{40})?( for [1-9][0-9]*)? of ([A-Za-z0-9-]+(\[bot\])?)$'
# comments <number>: each comment of <number>, one JSON object on each line, as GitHub lists them. They are
# read once in this step, and kept in $seen, a directory that the step makes for itself.
comments() {
  local file=$seen/comments-$1
  if [ ! -f "$file" ]; then
    gh api --paginate "repos/$REPO/issues/$1/comments" --jq '.[] | @json' > "$file.part" || return 1
    mv "$file.part" "$file"
  fi
  cat "$file"
}
# works: the start of a jq filter that defines work, the work that a hold comment's body (its input) holds.
# Each work has hold comments of its own, so that a hold of one work never takes the place of a hold of
# another, and the rescreen pass takes each work again. A hold that the rescreen pass tries again names its
# work in its marker: answer, draft or approve as the marker names the task, and review for a marker with no
# task (a rescreen takes it again). Any other hold names it in its title: answer ("Automated answer held."),
# draft ("Automated reply held."), approve ("Automated start of the checks held."), import ("Automated check
# for the import held."), catchup ("Automated close and reopen held."), and review for any other.
works='def work: (capture("\n<!-- review-held-(limit|cap|transient) [0-9]+(?: [0-9]+(?: (?<t>answer|draft|approve)(?: [1-9][0-9]*)?)?)? -->(\n|$)")
    | .t // "review")
  // (capture("^<!-- review-held -->\n[*][*]Automated (?<t>answer|reply|start of the checks|check for the import|close and reopen) held[.][*][*](\n|$)")
    | {"answer": "answer", "reply": "draft", "start of the checks": "approve", "check for the import": "import",
       "close and reopen": "catchup"}[.t])
  // "review"; '
# holds <number>: the newest hold comment of each work (works) on <number>, one on each line: "<work> <time>
# <run> <tries> <kind> <task> <comment> <id> <head>". For a hold that the rescreen pass tries again (its
# marker <!-- review-held-<kind> <run> <tries>[ <task>[ <comment>]] -->): <kind> is limit
# (OUTSIDE_HOURLY_LIMIT), cap (SCREENED_HOURLY_CAP) or transient (a screened review, answer or draft that
# failed or ran out of time), <run> the run of the event this hold comes from (a run that takes the hold
# again keeps it), <tries> the screened reviews of it that failed so far, <task> the task that takes it again
# (answer, draft or approve as the marker names it, and rescreen for a marker with no task), and <comment>
# the comment that a held answer answers (- for none). Each of <run> to <comment> is - for a hold that is not
# tried again (the screen held it, or its tries are used up). <id> is the id of the comment, and <head> the
# head that the hold names (- for none). Only github-actions[bot]'s comments count.
holds() {
  comments "$1" | jq -rs "$works"'map(select(.user.login == "github-actions[bot]"
      and ((.body // "") | startswith("<!-- review-held -->")))
      | {at: (.updated_at // "-"), id, body: (.body // "")} | .work = (.body | work))
    | group_by(.work)[] | max_by(.at)
    | "\(.work) \(.at) \((.body
        | capture("\n<!-- review-held-(?<kind>limit|cap|transient) (?<run>[0-9]+)(?: (?<tries>[0-9]+)(?: (?<task>answer|draft|approve)(?: (?<comment>[1-9][0-9]*))?)?)? -->(\n|$)")
        | "\(.run) \(.tries // "0") \(.kind) \(.task // "rescreen") \(.comment // "-")") // "- - - - -") \(
      .id) \((.body | capture("\n<!-- review-held-head (?<h>[0-9a-f]{40}) -->(\n|$)") | .h) // "-")"'
}
# limit_hold <number> <work>: the newest hold comment of <work> on <number> (holds), as "<time> <run> <tries>
# <kind> <task> <comment> <id> <head>". Nothing when <work> has no hold comment.
limit_hold() {
  local found
  found=$(holds "$1") || return 1
  awk -v w="$2" '$1 == w { sub(/^[^ ]+ /, ""); print }' <<< "$found"
}
# waiting <number> <author> <kind>: "<time> <id>" of each comment, review with a text and review comment of
# <author> on <number> (a pull request when <kind> is pr) that waits for an answer, oldest first, as the gather
# job lists them for an answer (answer-to.json): each one made after what the workflow's newest review, fix
# review, answer or hold read. A review and a fix review read the conversation when their run started, as
# their marker <!-- review-read <time> --> says (one with no such marker, from before it, when GitHub last
# changed it), so that a comment made while their run ran still waits. That marker counts only among the
# marker lines at the start of the comment, which the workflow writes: the text of a review of before the
# move off pull_request_target is the model's, with no change, and can hold any marker. An answer answers
# the comments up to the one that its marker names, the newest that waited for it, so that a comment made
# while it ran still waits too. A hold counts from the time GitHub last changed it. A hold that the workflow
# tries again as an answer answers nothing: each comment that waited when it was written, up to the one that
# its marker names, still waits until an answer answers it, whatever review or hold came after that hold.
waiting() {
  local found
  # shellcheck disable=SC2016 # $b is jq's
  found=$(comments "$1" | jq -c '(.body // "") as $b | {made: .created_at, at: .updated_at, id,
    author: .user.login, own: (if .user.login != "github-actions[bot]" then null
      elif ($b | startswith("<!-- review-held -->"))
           and ($b | test("\n<!-- review-held-[a-z]+ [0-9]+ [0-9]+ answer [0-9]+ -->(\n|$)"))
      then {held: ($b | capture("\n<!-- review-held-[a-z]+ [0-9]+ [0-9]+ answer (?<c>[0-9]+) -->") | .c)}
      elif ($b | test("^<!-- review-answer [0-9]+")) then {answers: ($b | capture("^<!-- review-answer (?<c>[0-9]+)") | .c)}
      elif ($b | test("^<!-- review(-held)? -->")) then {read: (($b
        | capture("^<!-- review(-held|-fix [0-9a-f]{40})? -->(\n<!-- review-(head|verdict|screened) [^\n]* -->)*\n<!-- review-read (?<t>[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z) -->(\n|$)")
        | .t) // .updated_at)}
      else null end)}') \
    || return 1
  if [ "$3" = pr ]; then
    # shellcheck disable=SC2016 # $b is jq's
    found+=$'\n'$(gh api --paginate "repos/$REPO/pulls/$1/reviews" --jq '.[] | (.body // "") as $b
      | {made: .submitted_at, at: .submitted_at, id, author: .user.login, text: ($b | test("\\S")),
         own: (if .user.login == "github-actions[bot]" and ($b | startswith("<!-- review-fix ")) then {read: (($b
           | capture("^<!-- review(-held|-fix [0-9a-f]{40})? -->(\n<!-- review-(head|verdict|screened) [^\n]* -->)*\n<!-- review-read (?<t>[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z) -->(\n|$)")
           | .t) // .submitted_at)} else null end)}
      | @json') || return 1
    found+=$'\n'$(gh api --paginate "repos/$REPO/pulls/$1/comments" \
      --jq '.[] | {made: .created_at, id, author: .user.login, own: null} | @json') || return 1
  fi
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  AUTHOR_OF=$2 jq -rs '(map(select(.author == $ENV.AUTHOR_OF) | {key: (.id | tostring), value: (.made // "")})
      | from_entries) as $made
    | ([.[] | select(.own.answers) | $made[.own.answers] // .at] | map(strings) | max // "") as $answered
    | [.[] | select(.own.read) | {read: .own.read, at}] as $reads
    | ($reads | map(.read) + [$answered] | map(strings) | max // "") as $since
    | [.[] | select(.own.held) | {upto: $made[.own.held], at} | select(.upto != null)] as $holds
    | .[] | select(.author == $ENV.AUTHOR_OF and .text != false and ((.made // "") as $m
        | $m > $since or any($holds[]; . as $h | $m <= $h.upto and $m > $answered
            and $m > ([$reads[] | select(.at < $h.at) | .read] | map(strings) | max // ""))))
    | "\(.made) \(.id)"' <<< "$found" | sort
}
# held_account <run> <author>: the account whose limit a hold of <run>, on an item of <author>, counts on,
# when <run> is a run of review.yml (by its path): the account that started it, for a run of issues or
# issue_comment; for a CI run's (workflow_run), the account that its screen job names (screen <account>),
# on whose limit its trust job counted it, and for one with no such job (its screen job was skipped at the
# limit, and GitHub can list a skipped job with its name not filled in), the account that the trust job
# counts such a run on: <author> when neither <author> nor the account that started it has write access,
# else that account; the account its name ends with, for a run that github-actions[bot] started (the
# rescreen pass's) with one of the pass's names (titled); the account that started it, for a run by hand of
# an App in APPS or of an account with write access (trusted), which has no limit. Nothing for any other run,
# or when GitHub no longer has it (a deleted or expired run). It fails when GitHub could not say.
held_account() {
  local run path event login title names name a=0 rc=0
  local named='^screen ([A-Za-z0-9-]+(\[bot\])?)$'
  [[ $1 =~ ^[1-9][0-9]*$ ]] || return 0
  run=$(gh api "repos/$REPO/actions/runs/$1" \
    --jq '"\(.path // "-") \(.event) \(.actor.login) \(.display_title // "" | gsub("[\r\n]"; " "))"' 2>&1) \
    || { [[ $run == *"(HTTP 404)"* ]] || return 1; return 0; }
  read -r path event login title <<< "$run"
  [[ $path == '.github/workflows/review.yml' && $login =~ ^[A-Za-z0-9-]+(\[bot\])?$ ]] || return 0
  case $event in
    issues|issue_comment) echo "$login" ;;
    workflow_run)
      names=$(gh api --method GET --paginate "repos/$REPO/actions/runs/$1/jobs" -F per_page=100 \
        --jq '.jobs[] | .name // ""' 2>&1) || { [[ $names == *"(HTTP 404)"* ]] || return 1; names=""; }
      while IFS= read -r name; do
        if [[ $name =~ $named ]]; then
          echo "${BASH_REMATCH[1]}"
          return 0
        fi
      done <<< "$names"
      if [[ ${2:-} =~ ^[A-Za-z0-9-]+(\[bot\])?$ ]]; then
        trusted "$2" || a=$?
        trusted "$login" || rc=$?
        (( a != 2 && rc != 2 )) || return 1
        if (( a != 0 && rc != 0 )); then
          echo "$2"
          return 0
        fi
      fi
      echo "$login" ;;
    workflow_dispatch)
      if [ "$login" = 'github-actions[bot]' ]; then
        if [[ $title =~ $titled ]]; then echo "${BASH_REMATCH[5]}"; fi
      else
        trusted "$login" || rc=$?
        (( rc != 2 )) || return 1
        (( rc != 0 )) || echo "$login"
      fi ;;
  esac
}
# head_marks <number> <head>: what the comments of github-actions[bot] on <number> say of <head>, as
# "<review> <held> <conflict> <caught> <steered>", from the lines that the workflow writes alone, never from
# the text of a review: the model writes that text, and a review of before the move off pull_request_target
# holds it with no change, so it can name any commit and hold any marker. review is new when a comment starts
# with <!-- review --> and, on its next line, the marker <!-- review-head <head> --> of this workflow's review;
# old when its first two lines are <!-- review --> and "**Automated review** of commit " with the first 12
# characters of <head>, the header of the review of before that move (a review of now has the marker of its
# head on its second line, so it is never old); and none else. held is true when a hold comment names <head>
# (<!-- review-held-head <head> -->). conflict is true when the label comment holds
# <!-- review-conflict-state <head> -->: <head> waits on its author for a merge conflict. caught is true when
# the label comment holds <!-- review-catchup <head> -->: a catch-up closed and reopened the pull request at
# <head>. steered is true when the label comment holds <!-- review-steering <head> -->: <head> changes a file
# under .github/, so the post job approves no run of it, and a person at Theorem approves its runs.
head_marks() {
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  comments "$1" | SHA=$2 jq -rs 'map(select(.user.login == "github-actions[bot]") | .body // "") as $b
    | [(if any($b[]; startswith("<!-- review -->\n<!-- review-head " + $ENV.SHA + " -->\n")) then "new"
        elif any($b[]; . + "\n"
          | startswith("<!-- review -->\n**Automated review** of commit " + $ENV.SHA[0:12] + "\n")) then "old"
        else "none" end),
       any($b[]; startswith("<!-- review-held -->")
         and test("\n<!-- review-held-head " + $ENV.SHA + " -->(\n|$)")),
       any($b[]; startswith("<!-- review-label -->")
         and test("\n<!-- review-conflict-state " + $ENV.SHA + " -->(\n|$)")),
       any($b[]; startswith("<!-- review-label -->")
         and test("\n<!-- review-catchup " + $ENV.SHA + " -->(\n|$)")),
       any($b[]; startswith("<!-- review-label -->")
         and test("\n<!-- review-steering " + $ENV.SHA + " -->(\n|$)"))] | map(tostring) | join(" ")'
}
# no_key_of <number> <head>: true when the label comment of github-actions[bot] on <number> holds
# <!-- review-no-key <head> -->: the screen passed <head> while the environment post held no key of
# the OSS Verify App, so the post job approved no run of it, and a person at Theorem approves its runs.
no_key_of() {
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  comments "$1" | SHA=$2 jq -rs 'any(.[]; .user.login == "github-actions[bot]" and ((.body // "")
    | startswith("<!-- review-label -->") and test("\n<!-- review-no-key " + $ENV.SHA + " -->(\n|$)")))'
}
# relabel_withdraws <number> <head>: why a relabel of <head> withdraws the import check run of <head>, from the
# comments of github-actions[bot] on <number>, by the rule that the post job of that relabel reads (rules.py
# verdict, its why). screen when a hold comment of the screen that names <head> (its text holds "The automated screen
# held ", and it has no marker of a hold that is tried again) is newer than each review comment of <head> whose run
# screened it (the marker <!-- review-screened <head> --> on the line after the marker of its verdict): the state
# held. Else blocking or person, of the newest review comment of <head> newer than the newest screened one (of any,
# when none is screened) that gives one, or of the newest screened review comment when it does not pass. Else -: then
# a relabel of <head> withdraws nothing. It records an import check run only when the newest review comment of <head>
# holds the marker and passes (rules.py verdict, screened). A relabel that withdraws records none.
relabel_withdraws() {
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  comments "$1" | SHA=$2 jq -rs '[.[] | select(.user.login == "github-actions[bot]")
      | {at: (.updated_at // ""), body: (.body // "")}] as $ours
    | [$ours[] | select(.body | startswith("<!-- review -->\n<!-- review-head " + $ENV.SHA + " -->\n"))
        | .at as $at | (.body | split("\n")) as $l
        | ($l[2] // "" | capture("^<!-- review-verdict " + $ENV.SHA + " (?<v>pass|blocking|person)( will-fix)? -->$"))
        | {at: $at, verdict: .v, screened: ($l[3] == "<!-- review-screened " + $ENV.SHA + " -->")}] as $reviews
    | ([$reviews[] | select(.screened) | .at] | max // "") as $screened
    | ([range(0; $reviews | length) | select($reviews[.].screened)] | last) as $last
    | ([$reviews[(($last // -1) + 1):][] | .verdict | select(IN("blocking", "person"))] | last) as $newer
    | ([$ours[] | select(.body | startswith("<!-- review-held -->")
          and test("\n<!-- review-held-head " + $ENV.SHA + " -->(\n|$)")
          and (test("\n<!-- review-held-(limit|cap|transient) [0-9]+"
            + "( [0-9]+( [a-z]+( [1-9][0-9]*)?)?)? -->(\n|$)") | not)
          and contains("The automated screen held "))
        | .at] | max // "") as $held
    | if $held != "" and $held > $screened then "screen"
      elif $newer != null then $newer
      elif $last != null and ($reviews[$last].verdict | IN("blocking", "person")) then $reviews[$last].verdict
      else "-" end'
}
# gave_up <number>: true when a hold comment of github-actions[bot] on <number> says that the workflow closed
# it and could not reopen it. The catch-up then tries nothing more on it.
gave_up() {
  comments "$1" | jq -rs 'any(.[]; .user.login == "github-actions[bot]" and ((.body // "")
    | startswith("<!-- review-held -->")
      and contains("\n\nThe workflow closed this pull request so that GitHub starts its checks. It could not reopen the pull request after ")))'
}
# pages: the start of the --jq filter of a list of runs, which gives, before the rows of each page, the line
# "= <total_count> <runs on the page>" that whole reads.
pages='"= \(.total_count // (.workflow_runs | length)) \(.workflow_runs | length)", '
# whole: the rows of a list of runs read with pages, from standard input. It fails, with no row, when GitHub
# cut the list: GitHub gives at most 1,000 runs for a list with created, event, head_sha or status, the newest
# first, and its total_count then says that more runs match.
whole() {
  awk '$1 == "=" { if ($2 > total) total = $2; listed += $3; next } { rows[++n] = $0 }
    END { if (listed < total) exit 3; for (i = 1; i <= n; i++) print rows[i] }'
}
# runs_in <event> <created> <filter>: the rows that <filter> (a --jq filter that starts with pages) gives of
# this workflow's runs of <event> created in <created>: from the start of a day on (>=<day>T00:00:00Z), on a
# day (<day>), or in an hour of a day. A list that GitHub cut is read again one day at a time, and the list of
# a day one hour at a time. It fails when GitHub could not say, or when it cut the list of an hour.
runs_in() {
  local out rows day today hour
  out=$(gh api --method GET --paginate "repos/$REPO/actions/workflows/review.yml/runs" -f event="$1" \
    -f created="$2" -F per_page=100 --jq "$3") || return 1
  if rows=$(whole <<< "$out"); then
    [ -z "$rows" ] || printf '%s\n' "$rows"
    return 0
  fi
  case $2 in
    '>='[0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9]T00:00:00Z)
      day=${2:2:10} today=$(date -u +%Y-%m-%d)
      while [[ ! $day > $today ]]; do
        runs_in "$1" "$day" "$3" || return 1
        day=$(date -u -d "$day +1 day" +%Y-%m-%d)
      done ;;
    [0-9][0-9][0-9][0-9]-[0-9][0-9]-[0-9][0-9])
      for hour in $(seq -w 0 23); do
        runs_in "$1" "${2}T$hour:00:00Z..${2}T$hour:59:59Z" "$3" || return 1
      done ;;
    *) echo "::error::GitHub lists at most 1,000 runs of $1 created $2, and more of them match." >&2; return 1 ;;
  esac
}
# ci_of <head> <repository> <branch>: the CI runs of <head> of the event pull_request from the head repository
# <repository> and its branch <branch>, the runs of a pull request's own head: another fork's runs of the same
# commit, held or not, are not its CI. pending while one of them is queued, in progress, waiting or held for a
# person's approval, or while GitHub does not list them all (whole); else the time when the newest one ended;
# nothing when there is none. GitHub lists a held run with the status action_required, or with the status
# completed and the conclusion action_required (run 39977702978 of this repository, read 2026-11-17): such a
# run has not ended.
ci_of() {
  local out rows
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  out=$(SHA=$1 REPOSITORY=$2 BRANCH=$3 gh api --method GET --paginate "repos/$REPO/actions/runs" \
    -f head_sha="$1" -F per_page=100 --jq "$pages"'(.workflow_runs[]
      | select(.head_sha == $ENV.SHA and .event == "pull_request" and .path == ".github/workflows/ci.yml"
               and ((.head_repository.id // 0) | tostring) == $ENV.REPOSITORY
               and .head_branch == $ENV.BRANCH)
      | if .status == "completed" and .conclusion != "action_required" then .updated_at // "-" else "pending"
        end)') || return 1
  if ! rows=$(whole <<< "$out"); then echo pending; return 0; fi
  sort <<< "$rows" | awk '$0 == "pending" { p = 1 } NF { last = $0 } END { print (p ? "pending" : last) }'
}
# pusher <head> <repository> <branch>: the account that started the newest of the CI runs that ci_of reads (by
# when GitHub made it): the actor of that run, whose action the trust job screens on that run's own event
# (workflow_run). Nothing when there is no such run, or when GitHub names no account of it. It fails when GitHub
# could not say, or does not list them all (whole).
pusher() {
  local out rows login
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  out=$(SHA=$1 REPOSITORY=$2 BRANCH=$3 gh api --method GET --paginate "repos/$REPO/actions/runs" \
    -f head_sha="$1" -F per_page=100 --jq "$pages"'(.workflow_runs[]
      | select(.head_sha == $ENV.SHA and .event == "pull_request" and .path == ".github/workflows/ci.yml"
               and ((.head_repository.id // 0) | tostring) == $ENV.REPOSITORY
               and .head_branch == $ENV.BRANCH)
      | "\(.created_at // "-") \(.actor.login // "")")') || return 1
  rows=$(whole <<< "$out") || return 1
  login=$(sort <<< "$rows" | awk 'NF { last = $2 } END { print last }')
  [[ ! $login =~ ^[A-Za-z0-9-]+(\[bot\])?$ ]] || echo "$login"
}
hour=$(date -u -d '-1 hour' +%Y-%m-%dT%H:%M:%SZ)
quarter=$(date -u -d '-15 minutes' +%Y-%m-%dT%H:%M:%SZ)
first=$(date -u -d '-7 days' +%Y-%m-%d)
# kept: the review job of a run reads the pull request or the issue from the artifact review-data of the
# run's gather job, which GitHub deletes kept_days days after the gather job made it (its retention-days). The
# failed jobs of a run made before kept do not run again (rerun): a re-run starts at the next run of this pass
# and its review job takes the artifact up to an hour after that, when it may be gone.
kept_days=1
kept=$(date -u -d "-$(( kept_days * 24 - 1 )) hours" +%Y-%m-%dT%H:%M:%SZ)
failed=0
declare -A pr_of=() pr_head=() pr_base=() pr_draft=() pr_repo=() pr_ref=()
# read_pulls: the open pull requests, each with its head, its base, whether it is a draft, the id of its head
# repository (0 when that repository is gone) and its head branch, into pr_head, pr_base, pr_draft, pr_repo
# and pr_ref, and the numbers of the pull requests into main of each head into pr_of: a workflow_run's name
# gives its head, and no head repository or branch, so the run is taken as a run of the pull request into
# main with that head, or of the one of them that its trust job names when two forks pushed the same commit
# (reviewed), and of none into another branch, whose CI run starts no review.
read_pulls() {
  local pulls n sha base draft repository ref
  pulls=$(gh api --paginate "repos/$REPO/pulls?state=open&per_page=100" \
    --jq '.[] | "\(.number) \(.head.sha) \(.base.ref) \((.draft // false) | tostring) \(.head.repo.id // 0) \(
      .head.ref // "-")"') \
    || { echo "::error::the open pull requests could not be read."; return 1; }
  while read -r n sha base draft repository ref; do
    [[ ${n:-} =~ ^[1-9][0-9]*$ && ${sha:-} =~ ^[0-9a-f]{40}$ ]] || continue
    pr_head[$n]=$sha pr_base[$n]=$base pr_draft[$n]=$draft pr_repo[$n]=${repository:-0} pr_ref[$n]=${ref:--}
    [ "$base" != main ] || pr_of[$sha]+=" $n"
  done <<< "$pulls"
}
# row gives each run of review.yml on one line: "<id> <created> <ended> <status> <conclusion> <event>
# <started> <attempt> <name>", - for none (ended, for a run that is not completed); attempt is its
# run_attempt, 1 for its first.
row='def row: "\(.id) \(.created_at // "-") \(if .status == "completed"
  then (.updated_at // .created_at // "-") else "-" end) \(.status // "-") \(.conclusion // "-") \(.event) \(
  .run_started_at // .created_at // "-") \(.run_attempt // 1) \(.display_title // "" | gsub("[\r\n]"; " "))";'
# by_hand <day>: the workflow_dispatch runs of <day>, as rows.
by_hand() {
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  DAY=$1 runs_in workflow_dispatch "$1" "$row$pages"'(.workflow_runs[]
    | select(.event == "workflow_dispatch" and ((.created_at // "") | startswith($ENV.DAY))) | row)'
}
declare -A running=() reached=()
# jobs_of <run>: $seen/jobs-<run>, the jobs of <run>, one JSON object on each line, read once in this step.
jobs_of() {
  local file=$seen/jobs-$1
  [ ! -f "$file" ] || return 0
  gh api --method GET --paginate "repos/$REPO/actions/runs/$1/jobs" -F per_page=100 --jq '.jobs[] | @json' \
    > "$file.part" || return 1
  mv "$file.part" "$file"
}
# reviewed <run> <numbers>: of <numbers>, the pull requests into main of the head of the CI run <run>, the one
# that its trust job names in its notice: "#<n>: the task <task>, the route <route>." (route), or "No
# <task> of #<n>: <why>" (stop). Another fork can push the same commit and open a pull request of it into
# main: the trust job reviews each CI run as the run of its own pull request alone, by its head commit, head
# repository and head branch. None of <numbers> when the trust job names another pull request (one into
# another branch). All of <numbers> when its pull request cannot be told: its trust job names none (the CI
# run of a head that more than one open pull request has, which is the run of none of them alone, or a run
# from before the notice), or its jobs or its notices cannot be read. The run is then taken as a run of each.
reviewed() {
  local check notes line n=""
  local routed='^#([1-9][0-9]*): the task [a-z]+, the route [a-z]+\.$'
  local halted='^No [a-z]+ of #([1-9][0-9]*): '
  if ! jobs_of "$1"; then echo "$2"; return 0; fi
  check=$(jq -r 'select(.name == "trust") | .check_run_url // "" | split("/") | last' "$seen/jobs-$1" \
    | head -n 1)
  if ! [[ $check =~ ^[1-9][0-9]*$ ]]; then echo "$2"; return 0; fi
  if ! notes=$(gh api --method GET --paginate "repos/$REPO/check-runs/$check/annotations" -F per_page=100 \
    --jq '.[] | select(.annotation_level == "notice") | .message // "" | gsub("[\r\n]"; " ")'); then
    echo "$2"
    return 0
  fi
  while IFS= read -r line; do
    if [[ $line =~ $routed || $line =~ $halted ]]; then
      n=${BASH_REMATCH[1]}
      break
    fi
  done <<< "$notes"
  if [ -z "$n" ]; then
    echo "$2"
  elif [[ " $2 " == *" $n "* ]]; then
    echo "$n"
  fi
}
# take <file>: each run of the rows of <file> that names an item, into $seen/runs: "<id> <created> <ended>
# <status> <conclusion> <event> <number> <task> <head> <comment> <account> <started> <attempt>", - for none. A
# name gives its task and its item (run-name): #<n> ends at a space or at the end of the name, so that #12 is
# never #123, and a workflow_run's name gives its head, which the open pull requests into main map to the
# pull request into main with that head (pr_of), or, when more than one into main has it, to the one that the
# run's trust job names (reviewed). The comment of a stop's name is the stop. An item with a run that has not
# finished, of any task, gets no run (running). The run of this step (RUN_ID, the run of a stop whose trust
# job decides it again) is not one of them.
take() {
  local id created ended status conclusion event started attempt title number task head comment account
  local numbers
  local named='^(review|answer|draft|reply|rescreen|approve|catchup|conflict|relabel|stop) #([1-9][0-9]*)( at ([0-9a-f]{40}))?( for ([1-9][0-9]*|[a-z-]+))?( of ([A-Za-z0-9-]+(\[bot\])?))?$'
  local pushed='^review ([0-9a-f]{40}) by '
  local opened='^review #([1-9][0-9]*)$'
  local answered='^answer #([1-9][0-9]*) for ([1-9][0-9]*) by '
  while read -r id created ended status conclusion event started attempt title; do
    [[ ${id:-} =~ ^[1-9][0-9]*$ ]] || continue
    [ "$id" != "${RUN_ID:-}" ] || continue
    numbers="" task="" head=- comment=- account=-
    case $event in
      workflow_dispatch)
        [[ ${title:-} =~ $named ]] || continue
        task=${BASH_REMATCH[1]} numbers=${BASH_REMATCH[2]} head=${BASH_REMATCH[4]:--}
        comment=${BASH_REMATCH[6]:--} account=${BASH_REMATCH[8]:--} ;;
      workflow_run)
        [[ ${title:-} =~ $pushed ]] || continue
        task=review head=${BASH_REMATCH[1]}
        numbers=${pr_of[$head]:-}
        [[ ${numbers# } != *" "* ]] || numbers=$(reviewed "$id" "$numbers" < /dev/null) ;;
      issues)
        [[ ${title:-} =~ $opened ]] || continue
        task=review numbers=${BASH_REMATCH[1]} ;;
      issue_comment)
        [[ ${title:-} =~ $answered ]] || continue
        task=answer numbers=${BASH_REMATCH[1]} comment=${BASH_REMATCH[2]} ;;
      *) continue ;;
    esac
    for number in $numbers; do
      [ "$status" = completed ] || running[$number]=1
      echo "$id $created $ended $status $conclusion $event $number $task $head $comment $account $started" \
        "${attempt:--}" >> "$seen/runs"
    done
  done < "$1"
}
# read_runs: review.yml's runs of the last 8 days that name an item, by their names, into $seen/runs (take):
# the workflow_dispatch runs one day at a time, and the runs of each event in one list from the first of those
# days.
# GitHub gives at most 1,000 runs for one list with created: a list that it cut is read again one day, then
# one hour, at a time, and a list of one hour that it cut fails this read (runs_in).
read_runs() {
  local back day event
  : > "$seen/listed"
  for back in 7 6 5 4 3 2 1 0; do
    day=$(date -u -d "-$back days" +%Y-%m-%d)
    by_hand "$day" >> "$seen/listed" || { echo "::error::the runs of $day could not be read."; return 1; }
  done
  for event in workflow_run issue_comment issues; do
    # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
    EVENT=$event FROM="${first}T00:00:00Z" runs_in "$event" ">=${first}T00:00:00Z" "$row$pages"'(.workflow_runs[]
      | select(.event == $ENV.EVENT and (.created_at // "") >= $ENV.FROM) | row)' \
      >> "$seen/listed" || { echo "::error::the runs of the event $event could not be read."; return 1; }
  done
  : > "$seen/runs"
  take "$seen/listed"
}
# reach <day>: the workflow_dispatch runs of each day from <day> to the day before the first of the 8 days, each
# day listed once, into $seen/runs: a catch-up left closed reads back to the day before its close.
reach() {
  local day=$1
  while [[ $day < $first ]]; do
    if [ -z "${reached[$day]:-}" ]; then
      by_hand "$day" > "$seen/back-$day" || { echo "::error::the runs of $day could not be read."; return 1; }
      take "$seen/back-$day"
      reached[$day]=1
    fi
    day=$(date -u -d "$day +1 day" +%Y-%m-%d)
  done
}
# facts <run>: what the jobs of <run> show, read once: "<signin> <screen> <post> <settled> <early> <reviewed>
# <commented> <held> <counts>", - for none. signin: a step whose name starts with "Sign in" failed in a job of
# the run, which so judged nothing. screen: the conclusion of its screen job. post: the conclusion of its post
# job, signin for one that failed at such a step and failure for one that failed at another (a write of the
# App, say). settled: its post job approved held runs or recorded the import check run. early: stopped when
# its trust job stopped it (the job was skipped, or every job after it was), conflict when the comment job
# alone ran after it (the task conflict). reviewed: signin when its review job failed at such a step.
# commented: the conclusion of its comment job, which posts the review, the answer or the label comment of a
# draft (success when it did, failure or cancelled when it posted nothing or not all), or left when that job
# left its answer to a later run (its step of that name ran): another run answered a comment of that answer
# first, so it posted nothing of its own. held: held when its hold job ran, so the run itself posted nothing.
# counts: count when the run counts toward the limit of the
# account that its name ends with, as the trust job's earlier counts it (not a run that its trust job
# refused, nor one whose screen could not sign in; a run whose screen passed and whose review then could not
# sign in counts, once: its screen ran, and its failed jobs run again with no new screen), else skip. The job
# rescreen, which review.yml had before this pass moved to rescreen.yml and which each of its runs skipped, is
# none of the run's jobs.
facts() {
  local file=$seen/jobs-$1
  jobs_of "$1" || return 1
  jq -rs 'def signed_out:
      any(.steps[]?; ((.name // "") | startswith("Sign in")) and .conclusion == "failure");
    (map(select(.name == "trust")) | first) as $t | (map(select(.name == "post")) | first) as $p
    | map(select(.name != "trust" and .name != "rescreen")) as $rest
    | [(if any(.[]; signed_out) then "signin" else "-" end),
       ((map(select(.name | test("^screen( |$)"))) | first | .conclusion) // "-"),
       (if $p == null then "-" elif $p.conclusion != "failure" then ($p.conclusion // "running")
        elif ($p | signed_out) then "signin" else "failure" end),
       (if $p != null and any($p.steps[]?; .conclusion == "success" and (.name
          | IN("Approve the held runs of the screened head", "Record the import check of the head")))
        then "settled" else "-" end),
       (if $t == null then "-" elif $t.conclusion == "skipped" then "stopped"
        elif $t.status == "completed" and ($rest | length) > 0 and ($rest | all(.conclusion == "skipped"))
        then "stopped"
        elif [$rest[] | select(.conclusion != "skipped") | .name] == ["comment"] then "conflict"
        else "-" end),
       (if any($rest[] | select(.name | test("^review( |$)")); signed_out) then "signin" else "-" end),
       ((map(select(.name == "comment")) | first) as $c
        | if $c == null then "-"
          elif any($c.steps[]?; .name == "Leave the answer to a later run" and .conclusion == "success")
          then "left" else ($c.conclusion // "running") end),
       (if any(.[]; .name == "hold" and .conclusion == "success") then "held" else "-" end),
       (if $t == null then "count" elif $t.conclusion == "skipped" then "skip"
        elif $t.status == "completed" and ($rest | length) > 0 and ($rest | all(.conclusion == "skipped"))
        then "skip"
        elif any($rest[] | select(.name | test("^screen( |$)")); signed_out) then "skip"
        else "count" end)] | join(" ")' "$file"
}
declare -A owed=() access=()
# access_of <login>: access[<login>], trusted's answer for <login>, 0 or 1, kept for this run. It fails when
# GitHub could not say.
access_of() {
  local rc=0
  [ -z "${access[$1]:-}" ] || return 0
  trusted "$1" || rc=$?
  (( rc != 2 )) || { echo "::error::GitHub did not say whether $1 has write access."; return 1; }
  access[$1]=$rc
}
# held_of: held_list, "<head> <repository> <branch> <created>" of each run of the event pull_request that
# GitHub holds for a person's approval, read once in this run, with the id of its head repository (0 when
# GitHub gives none) and its head branch: the runs that the filter status=action_required lists, with the
# status action_required, or with the status completed and the conclusion action_required, as GitHub lists a
# held run (ci_of). GitHub lists at most 1,000 of them, the newest first: when it cut the list, held_list is
# empty and held_cut is set, and held_at reads the runs of each head.
held_list="" held_read="" held_cut=""
held_of() {
  local out
  [ -z "$held_read" ] || return 0
  out=$(gh api --method GET --paginate "repos/$REPO/actions/runs" -f status=action_required \
    -f event=pull_request -F per_page=100 --jq "$pages"'(.workflow_runs[]
      | select((.status == "action_required" or .conclusion == "action_required")
               and .event == "pull_request")
      | "\(.head_sha) \(.head_repository.id // 0) \(.head_branch // "-") \(.created_at // "-")")') || return 1
  held_list=$(whole <<< "$out") || held_cut=1
  held_read=1
}
# held_at <head> <repository> <branch>: after held_of, when each run of <head> from the head repository
# <repository> and its branch <branch> that GitHub holds was made, one on each line. The held runs of a pull
# request are the runs of its head from its own head repository and head branch, the runs that the post job
# approves, never another run of the same commit: another account can push that commit to its own fork and
# open a pull request of it, whose runs GitHub holds too. None for a pull request whose head repository is
# gone (0): the post job approves no run of it. When GitHub cut the list of the runs of every head, the runs
# of <head> alone are read: the newest come first, so that list gives whether <head> has one and when the
# newest was made, cut or not.
held_at() {
  local h r b c
  [[ $2 =~ ^[1-9][0-9]*$ ]] || return 0
  if [ -z "$held_cut" ]; then
    while read -r h r b c; do
      if [[ $h == "$1" && $r == "$2" && $b == "$3" ]]; then echo "$c"; fi
    done <<< "$held_list"
    return 0
  fi
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  SHA=$1 REPOSITORY=$2 BRANCH=$3 gh api --method GET --paginate "repos/$REPO/actions/runs" -f head_sha="$1" \
    -f status=action_required -F per_page=100 --jq '.workflow_runs[]
      | select((.status == "action_required" or .conclusion == "action_required")
               and .head_sha == $ENV.SHA and .event == "pull_request"
               and ((.head_repository.id // 0) | tostring) == $ENV.REPOSITORY
               and .head_branch == $ENV.BRANCH) | .created_at // "-"'
}
: > "$seen/due"
# owe <at> <task> <account> <head> <comment> <why>: #number is due a run of <task>, for <account> (empty for
# none), at most one for each item and task. The runs start oldest <at> (when the reason began) first.
owe() {
  local key=$number:$2
  [ -z "${owed[$key]:-}" ] || return 0
  owed[$key]=1
  echo "$1 $number $2 ${3:--} ${4:--} ${5:--} $6" >> "$seen/due"
}
# runs_of <tasks> [<head>] [<event>]: "<created> <ended> <run>" of each run of #number of a task of <tasks>
# (a regular expression), of <head> and of <event> when they are given, oldest first.
runs_of() {
  awk -v n="$number" -v re="^($1)\$" -v h="${2:-}" -v e="${3:-}" '$7 == n && $8 ~ re &&
    (h == "" || $9 == h) &&
    (e == "" || $6 == e) { print $2, $3, $1 }' "$seen/runs" | sort
}
# marks_of: marks, the markers of the label comment of #number that this pass reads, one on each line: draft
# for the stored draft of its reply, and replied for a reply that posted.
marks_of() {
  [ -z "$marks_read" ] || return 0
  marks=$(comments "$number" | jq -r 'select(.user.login == "github-actions[bot]"
      and ((.body // "") | startswith("<!-- review-label -->")))
    | (if (.body | test("(^|\n)<!-- issue-draft [0-9]+-[0-9]+ -->(\n|$)")) then "draft" else empty end),
      (if (.body | test("(^|\n)<!-- issue-reply-posted [0-9]+ -->(\n|$)")) then "replied" else empty end)' \
    | sort -u) || { echo "::error::the comments of #$number could not be read."; return 1; }
  marks_read=1
}
# waits_of: waits, the comments of the author of #number that wait for an answer (waiting).
waits_of() {
  [ -z "$waits_read" ] || return 0
  waits=$(waiting "$number" "$author" "$kind") \
    || { echo "::error::the comments of #$number could not be read."; return 1; }
  waits_read=1
}
: > "$seen/stops"
# halt <stop> <fact> <work> <title> <text>: the work of #number is not tried again, at a bound of its tries
# (stopped, head_stopped, left_stopped and answer_stopped). The rescreen pass writes nothing for it: it starts
# a run of review.yml with the task stop, named "stop #<n>[ at <head>] for <stop>", at most one for each item
# in each of its runs. The trust job of that run decides the stop again with these functions, and gives its
# comment job the stop as halt wrote it to $seen/stops: the state label of <fact> (tries_used_up, or
# left_closed for a catch-up left closed), with Sami's next step in the label comment, then the hold comment
# with <title> and <text>, which names the head of a pull request and holds no marker of a hold that is tried
# again, in the place of the newest hold comment of <work> (works) that it read, or as a new one: never in
# the place of a hold of other work. The run of the pass fails for it.
halt() {
  local line at id
  failed=1
  line=$(limit_hold "$number" "$3") || { echo "::error::the comments of #$number could not be read."; return 1; }
  read -r at _ _ _ _ _ id _ <<< "$line"
  jq -nc --arg stop "$1" --arg fact "$2" --arg id "${id:-}" --arg title "$4" --arg text "$5" \
    --arg head "${head:-}" '{stop: $stop, fact: $fact, id: $id, title: $title, text: $text, head: $head}' \
    >> "$seen/stops"
  owe "${at:-$hour}" stop "" "${head:-}" "$1" "its work is not tried again"
}
# stopped <task> <tries>: the work of the hold that held_work read is not tried again, after <tries> runs of
# <task> since the hold (halt, with the stop hold-<work>): waits-on-theorem, with the label comment's step
# "Sami starts again, by hand, the work that the hold comment names", and a hold comment that says so in the
# place of that hold. The hold comment of other work stays as it is.
stopped() {
  local title work what tried of=$1
  [ "$of" != rescreen ] || of=review
  echo "::error::#$number: $1 ran $2 times since its hold at $h_at, with no new hold and nothing posted: it" \
    "is not tried again, and the label comment names the next step for Sami."
  case $1 in
    answer) title="Automated answer held." work="the automated answer" ;;
    draft) title="Automated reply held." work="the automated reply" ;;
    approve) title="Automated start of the checks held." work="" ;;
    *) title="Automated review held." work="the automated review" ;;
  esac
  what="this issue"
  [ "$kind" != pr ] || what="this pull request"
  tried="The workflow tried $work again $2 times after it held $what, and none of these tries finished."
  [ -n "$work" ] || tried="The workflow held the start of the checks of $what. Then it tried $2 times to start them, and no try finished."
  halt "hold-$of" tries_used_up "$of" "$title" "$tried The workflow does not try it again. You do not need to do anything."
}
# head_stopped <work> <tries>: the automated <work> (review; approval, of the held runs; import, the import
# check; or catchup) of the head of #number did not finish after <tries> tries, and is not tried again (halt,
# with the stop head-<work>): waits-on-theorem, with the label comment's step "Sami starts again, by hand, the
# work that the hold comment names", then a hold comment that says so and names the head, in the place of the
# newest hold comment of that work (works), and never of a hold of other work, which the rescreen pass still
# takes again. That hold stops each later try of the head, and no other reason takes the head in this run
# (taken).
head_stopped() {
  local title text of=catchup commit="the head commit ${head:0:12}"
  taken=1
  case $1 in
    review) of=review title="Automated review held." text="The automated review of $commit did not finish after $2 tries." ;;
    approval)
      of=approve title="Automated start of the checks held."
      text="The workflow tried $2 times to start the checks of $commit, and no try finished." ;;
    import)
      of=import title="Automated check for the import held."
      text="The automated check of $commit for the import into the internal repository did not finish after $2 tries." ;;
    *)
      title="Automated close and reopen held."
      text="The workflow tried $2 times to close and reopen this pull request so that GitHub starts the checks of $commit. No try finished." ;;
  esac
  echo "::error::#$number at $head: $text It is not tried again, and the label comment names the next step" \
    "for Sami."
  halt "head-$of" tries_used_up "$of" "$title" "$text The workflow does not try it again."
}
# left_stopped <tries>: the catch-up that closed #number could not reopen it after <tries> runs that only
# reopen it, and is not tried again (halt, with the stop reopen): waits-on-theorem, with the label comment's
# step "Sami reopens the pull request", then a hold comment that says so, in the place of the newest hold
# comment of a catch-up. That comment ends each later read of the item's runs (gave_up).
left_stopped() {
  echo "::error::#$number: the automated catch-up closed it and could not reopen it after $1 tries: it is not" \
    "tried again, and the label comment names the next step for Sami."
  halt reopen left_closed catchup "Automated close and reopen held." \
    "The workflow closed this pull request so that GitHub starts its checks. It could not reopen the pull request after $1 tries."
}
# failures <tasks>: of the runs of the head of #number of a task of <tasks>, newest first, back to the newest
# whose post job succeeded, how many failed in the post job at a step that is not a sign-in (at most
# REVIEW_TRIES): each counts a try of the head.
failures() {
  local n=0 run f post
  while read -r _ _ run; do
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read." >&2; return 1; }
    read -r _ _ post _ <<< "$f"
    [ "$post" != success ] || break
    [ "$post" != failure ] || n=$((n + 1))
    (( n < REVIEW_TRIES )) || break
  done < <(runs_of "$1" "$head" | sort -r)
  echo "$n"
}
# held_as <work>: the newest hold of <work> on #number, of the holds that consider read (hold, as holds gives
# them): "<time> <run> <tries> <kind> <task> <comment> <id> <head>", nothing for none.
held_as() {
  awk -v w="$1" '$1 == w { sub(/^[^ ]+ /, ""); print }' <<< "$hold"
}
# due_held [<work>]: the work that each hold of #number names, labelled review-held, once the hold is over an
# hour old: the newest hold of its review, of its answer, of its draft and of its approval, each for itself
# (held_work), so that the hold of one work never keeps the rescreen pass from the hold of another. With
# <work>, the hold of that work alone.
due_held() {
  local work h_at h_origin h_task h_comment tried=""
  for work in review answer draft approve; do
    [[ -z ${1:-} || $work == "$1" ]] || continue
    read -r h_at h_origin _ _ h_task h_comment _ <<< "$(held_as "$work")"
    [[ -n ${h_origin:-} && $h_origin != - ]] || continue
    tried=1
    held_work || return 1
  done
  [ -n "$tried" ] || [ -n "${1:-}" ] \
    || echo "#$number: no hold that is tried again (the screen held it, or its tries are used up)."
}
# held_work: the work of the hold that due_held read (h_at, h_origin, h_task, h_comment), once that hold is
# over an hour old. It is due while its reason holds (an answer while its comment waits, a draft while none is
# stored), and while its hold is not settled: the newest run of its task since the hold had no post job that
# approved held runs or recorded the import check run, and no comment job that posted (its review, its answer
# or the label comment of its draft; not the comment on a merge conflict). Each other run of its task since
# the hold is a try that settled nothing (a review's hold is taken again as a rescreen, and counts the
# rescreens and the reviews), but a run that ended at a failed step whose name starts with "Sign in": that
# run judged nothing, counts no try, and the work is taken again (D19). After REVIEW_TRIES tries (stopped), or
# while the newest run of its task is under an hour old, it is not started. retaken holds the task of each
# hold that this takes, which the other reasons leave to it.
held_work() {
  local task=$h_task pattern since tries=0 newest="" created run latest="" f who
  local signin="" settled="" early="" commented=""
  retaken+=" $task"
  [[ $h_at =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$ ]] \
    || { echo "::error::#$number: its hold has no time."; return 1; }
  if [[ ! $h_at < $hour ]]; then
    echo "#$number: held at $h_at, less than an hour ago."
    return 0
  fi
  case $task in
    answer)
      if [ "$h_comment" = - ]; then
        echo "#$number: its hold of an answer names no comment: left alone."
        retaken=${retaken%" $task"}
        return 0
      fi
      waits_of || return 1
      if ! grep -q " $h_comment\$" <<< "$waits"; then
        echo "#$number: comment $h_comment waits for no answer, so its hold is settled."
        retaken=${retaken%" $task"}
        return 0
      fi ;;
    draft)
      marks_of || return 1
      if [ -n "$marks" ]; then
        echo "#$number: its draft is stored, or its reply posted, so its hold is settled."
        retaken=${retaken%" $task"}
        return 0
      fi ;;
  esac
  pattern=$task
  [ "$task" != rescreen ] || pattern='rescreen|review'
  since=$(runs_of "$pattern" "" workflow_dispatch | awk -v at="$h_at" '$1 >= at')
  # Each run of the task since the hold, oldest first: the facts of the newest stay, and each run but one that
  # could not sign in counts a try.
  while read -r created _ run; do
    [ -n "${run:-}" ] || continue
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r signin _ _ settled early _ commented _ <<< "$f"
    newest=$created latest=$run
    [ "$signin" = signin ] || tries=$((tries + 1))
  done <<< "$since"
  if [ "$settled" = settled ] || { [ "$commented" = success ] && [ "$early" = - ]; }; then
    echo "#$number: run $latest of $task approved the held runs, recorded the import check or posted, so" \
      "its hold is settled."
    retaken=${retaken%" $task"}
    return 0
  fi
  if (( tries >= REVIEW_TRIES )); then
    stopped "$task" "$tries"
    return
  fi
  if [ -n "$latest" ]; then
    # Spaced as the hold's own hour is, so that a short outage of GitHub does not use up the tries.
    if [[ ! $newest < $hour ]]; then
      echo "#$number: $task ran at $newest, less than an hour ago, with no new hold: tried again later."
      return 0
    fi
    if (( tries > 0 )); then
      echo "#$number: $tries runs of $task since its hold settled nothing; trying again."
    else
      echo "#$number: each run of $task since its hold could not sign in, which counts no try; trying again."
    fi
  fi
  who=$(held_account "$h_origin" "$author") || { echo "::error::run $h_origin could not be read."; return 1; }
  if [ -z "$who" ]; then
    echo "#$number: its hold names no run whose account this pass can tell: left alone."
    retaken=${retaken%" $task"}
    return 0
  fi
  # A rescreen counts on the account that the hold names; an answer, a draft and an approval on the outside
  # author, as the trust job names them.
  case $task in
    rescreen) owe "$h_at" rescreen "$who" "$head" - "held at $h_at, for $who" ;;
    answer) owe "$h_at" answer "$limited" - "$h_comment" "its answer held at $h_at" ;;
    draft) owe "$h_at" draft "$limited" - - "its draft held at $h_at" ;;
    approve) owe "$h_at" approve "$limited" "$head" - "its approval held at $h_at" ;;
  esac
}
# answer_stopped <comment> <tries>: the comment job of <tries> answer runs of <comment> failed, so its answer
# is not tried again (halt, with the stop answer-post): waits-on-theorem, with the label comment's step "Sami
# starts again, by hand, the work that the hold comment names", then a hold comment that says so, in the place of
# the newest hold comment of an answer. That hold is not tried again, so the comments before it wait for no
# answer (waiting).
answer_stopped() {
  local what="this issue"
  [ "$kind" != pr ] || what="this pull request"
  echo "::error::#$number: the comment job of $2 answer runs of comment $1 failed: the answer is not tried" \
    "again, and the label comment names the next step for Sami."
  halt answer-post tries_used_up answer "Automated answer held." "The workflow wrote the automated answer to your comment on $what $2 times, and could not post it. The workflow does not try it again. You do not need to do anything."
}
# due_answer: the answer to the newest comment of the author of #number that waits for one (waiting) and is
# over 15 minutes old, on an issue only after its first reply posted. The newest run that names the comment,
# of its own event (issue_comment) or of workflow_dispatch, took it, but one that its trust job stopped or that left its
# answer to a later run (another run answered a comment of it first), and but one that posted nothing of its
# own: it ended at a failed sign-in, its comment job failed or was cancelled (a GitHub error on the post, say,
# for which no hold job runs), or its hold job held it. Once for each comment, then
# once an hour while the newest run of that comment posted nothing so. After REVIEW_TRIES runs of the comment
# whose comment job failed or was cancelled, the answer is not tried again (answer_stopped): each of them ran
# the screen and the model. A hold of an answer that is tried again leaves the comments to that hold
# (due_held), which counts its tries.
due_answer() {
  local at id runs created ended run f signin early commented held tries=0
  if [ "$kind" = issue ]; then
    marks_of || return 1
    grep -qx replied <<< "$marks" || return 0
  fi
  [[ $retaken != *" answer"* ]] || return 0
  waits_of || return 1
  [ -n "$waits" ] || return 0
  read -r at id <<< "$(awk -v q="$quarter" '$1 < q' <<< "$waits" | tail -n 1)"
  if [ -z "${id:-}" ]; then
    echo "#$number: a comment of $author waits for an answer, and is under 15 minutes old."
    return 0
  fi
  runs=$(awk -v n="$number" -v c="$id" '$7 == n && $8 == "answer" && $10 == c { print $2, $3, $1 }' \
    "$seen/runs" | sort)
  read -r created ended run <<< "$(tail -n 1 <<< "$runs")"
  if [ -n "${run:-}" ]; then
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r signin _ _ _ early _ commented held _ <<< "$f"
    if [[ $commented == failure || $commented == cancelled ]]; then
      while read -r _ _ run; do
        f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
        read -r _ _ _ _ _ _ commented _ <<< "$f"
        [[ $commented != failure && $commented != cancelled ]] || tries=$((tries + 1))
      done <<< "$runs"
      if (( tries >= REVIEW_TRIES )); then
        answer_stopped "$id" "$tries"
        return 0
      fi
    fi
    if (( tries > 0 )) || [[ $signin == signin || $held == held ]]; then
      if [[ ! $ended < $hour ]]; then
        echo "#$number: run $run of comment $id posted nothing (a failed sign-in, a failed comment job, or a" \
          "hold), less than an hour ago: tried again later."
        return 0
      fi
    elif [ "$early" != stopped ] && [ "$commented" != left ]; then
      echo "#$number: run $run took comment $id."
      return 0
    fi
  fi
  owe "$at" answer "$limited" - "$id" "comment $id of $author waits for an answer"
}
# due_draft: the draft of the reply to an outside issue whose label comment holds neither a stored draft nor
# a posted reply, once an hour after its newest draft run (of its issues event, by hand or of the pass) ended.
# Not after a hold that is not tried again (the issue waits on Sami), and not while a hold is tried again
# (due_held takes it).
due_draft() {
  local last
  marks_of || return 1
  [ -z "$marks" ] || return 0
  if [ -n "$(awk '$3 == "-"' <<< "$hold")" ]; then
    echo "#$number: its hold is not tried again, so its draft waits on Sami."
    return 0
  fi
  [ -z "$retaken" ] || return 0
  last=$(awk -v n="$number" '$7 == n && (($6 == "workflow_dispatch" && $8 == "draft") || $6 == "issues") {
    print $3 }' "$seen/runs" | sort | tail -n 1)
  if [ -n "$last" ] && [[ ! $last < $hour ]]; then
    echo "#$number: its draft run ended at $last, less than an hour ago: tried again later."
    return 0
  fi
  owe "${last:-$opened}" draft "$limited" - - "no draft of a reply to it is stored"
}
# due_approve: the approval of the runs of the head of #number that GitHub holds from its head repository and
# head branch (held_of and held_at), while no approval run screened the head with a verdict since the newest
# held run: its screen job passed and its post job did not fail (by the App's retry, one that failed leaves no
# verdict), or a hold that is not tried again, the newest of its work, names the head. Once an hour after the
# newest approval run of the head. A post job that failed at a step that is not a sign-in counts a try of the
# head; after REVIEW_TRIES of them, the head is not tried again (head_stopped). A hold of an approval that is
# tried again leaves it to that hold (due_held). Never for a head that the label comment records as one that
# changes a file under .github/ (head_marks, steered), or as one that the screen passed while the environment
# post held no key of the OSS Verify App (no_key_of): the post job approved no run of such a head.
due_approve() {
  local list n last created ended run f screen post tries keyless
  held_of || { echo "::error::the runs of $head could not be read."; return 1; }
  list=$(held_at "$head" "${pr_repo[$number]:-0}" "${pr_ref[$number]:--}") \
    || { echo "::error::the runs of $head could not be read."; return 1; }
  n=$(grep -c . <<< "$list" || true)
  (( n > 0 )) || return 0
  last=$(sort <<< "$list" | tail -n 1)
  [[ $retaken != *" approve"* ]] || return 0
  head_of || return 1
  if [ "$steered" = true ]; then
    echo "#$number: $head changes a file under .github/, as its label comment records, so a person at Theorem" \
      "approves its runs."
    return 0
  fi
  keyless=$(no_key_of "$number" "$head") || { echo "::error::the comments of #$number could not be read."; return 1; }
  if [ "$keyless" = true ]; then
    echo "#$number: its label comment records that a run screened $head while the environment post had no key of the" \
      "OSS Verify App. So a person at Theorem approves the runs of $head."
    return 0
  fi
  if [ -n "$(awk -v h="$head" -v last="$last" '$3 == "-" && $9 == h && $2 >= last' <<< "$hold")" ]; then
    echo "#$number: a hold that is not tried again names $head."
    return 0
  fi
  read -r created ended run <<< "$(runs_of approve "$head" workflow_dispatch | tail -n 1)"
  if [ -n "${run:-}" ]; then
    if [[ ! $ended < $hour ]]; then
      echo "#$number: approval run $run of $head ended at $ended, less than an hour ago."
      return 0
    fi
    if [[ ! $created < $last ]]; then
      f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
      read -r _ screen post _ <<< "$f"
      if [ "$screen" = success ] && [ "$post" != failure ] && [ "$post" != signin ]; then
        echo "#$number: run $run screened $head with a verdict."
        return 0
      fi
      if [ "$post" = failure ]; then
        tries=$(failures approve) || return 1
        if (( tries >= REVIEW_TRIES )); then
          head_stopped approval "$tries"
          return 0
        fi
      fi
    fi
  fi
  owe "$last" approve "$limited" "$head" - "GitHub holds $n runs of $head"
}
# due_retry <tasks> <task> <work>: the App's retry. When the post job of the newest run of the head of #number
# of a task of <tasks> failed, at a sign-in or at a write of the App, the head is due <task> again, once an
# hour after that run ended. A CI run that its trust job stopped is not that newest run: it posted nothing,
# and it can be the run of another pull request of the head (one into another branch). A post job that
# failed at a step that is not a sign-in counts a try of the head; after REVIEW_TRIES of them, the automated
# <work> of the head is not tried again (head_stopped <work>).
due_retry() {
  local created ended run event f post early tries
  while read -r created ended run event; do
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r _ _ post _ early _ <<< "$f"
    [ "$event" = workflow_run ] && [ "$early" = stopped ] || break
  done < <(awk -v n="$number" -v re="^($1)\$" -v h="$head" '$7 == n && $8 ~ re && $9 == h {
    print $2, $3, $1, $6 }' "$seen/runs" | sort -r)
  [ -n "${run:-}" ] || return 0
  [ "$post" = signin ] || [ "$post" = failure ] || return 0
  if [[ ! $ended < $hour ]]; then
    echo "#$number: the post job of run $run failed, less than an hour ago: tried again later."
    return 0
  fi
  if [ "$post" = failure ]; then
    tries=$(failures "$1") || return 1
    if (( tries >= REVIEW_TRIES )); then
      head_stopped "$3" "$tries"
      return 0
    fi
  fi
  owe "$ended" "$2" "" "$head" - "the post job of run $run failed"
}
# merge_of: merge, the mergeable_state of #number, read again once while GitHub has not computed it (its
# mergeable is null); null when it still has not, and then the head waits for the next run.
merge_of() {
  local data
  [ -z "$merge" ] || return 0
  for _ in 1 2; do
    data=$(gh api "repos/$REPO/pulls/$number" --jq '"\(.mergeable) \(.mergeable_state // "unknown")"') \
      || { echo "::error::pull request #$number could not be read."; return 1; }
    if [[ $data != null\ * ]]; then
      merge=${data#* }
      return 0
    fi
  done
  merge=null
}
# head_of: review, held, conflicted, caught and steered, what the comments of #number say of its head
# (head_marks), read once.
head_of() {
  local line
  [ -z "$head_read" ] || return 0
  line=$(head_marks "$number" "$head") \
    || { echo "::error::the comments of #$number could not be read."; return 1; }
  read -r review held conflicted caught steered <<< "$line"
  head_read=1
}
# ci_head: ci, what the CI runs of the head of #number from its head repository and head branch say (ci_of),
# read once.
ci_head() {
  [ -z "$ci_read" ] || return 0
  ci=$(ci_of "$head" "${pr_repo[$number]:-0}" "${pr_ref[$number]:--}") \
    || { echo "::error::the CI runs of $head could not be read."; return 1; }
  ci_read=1
}
# ci_over: whether the newest CI run of the head ended over an hour ago, with none still to finish (read by
# ci_head first).
ci_over() {
  case $ci in
    "") echo "#$number: no CI run of $head ended."; return 1 ;;
    pending) echo "#$number: a CI run of $head has not finished, and its review comes after it."; return 1 ;;
  esac
  [[ ! $ci < $hour ]] || return 0
  echo "#$number: the CI run of $head ended at $ci, less than an hour ago."
  return 1
}
# due_conflict: the merge conflict of the head of an outside pull request, decided from the label comment's
# line <!-- review-conflict-state <head> --> and the mergeable_state that GitHub gives now. A head with a
# conflict that the line does not name yet: a conflict run, which asks the author to resolve it and gives
# waits-on-author and the line. A head with the line whose conflict is gone, with no push: a relabel, which
# sets its label again from what the workflow wrote of it and takes the line out. Each relabel of the head
# since the line counts: one that its trust job refused is started again at the next run, one that ran an
# hour after it ended, and after REVIEW_TRIES of them the head is not tried again (head_stopped). While the
# head has a conflict or the line, or GitHub has not computed its merge state, no other reason takes it
# (taken).
due_conflict() {
  local at since tries ended run f early
  merge_of || return 1
  if [ "$merge" = null ]; then
    echo "#$number: GitHub has not computed whether $head has a merge conflict: left for the next run."
    taken=1
    return 0
  fi
  if [ "$conflicted" = false ]; then
    [ "$merge" = dirty ] || return 0
    taken=1
    owe "$opened" conflict "" "$head" - "$head has a merge conflict"
    return 0
  fi
  taken=1
  if [ "$merge" = dirty ]; then
    echo "#$number: $head still has the merge conflict that its label comment names: its author's step."
    return 0
  fi
  at=$(comments "$number" | jq -rs '[.[] | select(.user.login == "github-actions[bot]"
      and ((.body // "") | startswith("<!-- review-label -->"))) | .updated_at // ""] | max // ""') \
    || { echo "::error::the comments of #$number could not be read."; return 1; }
  since=$(runs_of relabel "$head" workflow_dispatch | awk -v at="$at" '$1 >= at')
  tries=$(grep -c . <<< "$since" || true)
  if (( tries >= REVIEW_TRIES )); then
    head_stopped import "$tries"
    return 0
  fi
  if (( tries > 0 )); then
    read -r _ ended run <<< "$(tail -n 1 <<< "$since")"
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r _ _ _ _ early _ <<< "$f"
    if [ "$early" != stopped ] && [[ ! $ended < $hour ]]; then
      echo "#$number: relabel run $run of $head ended at $ended, less than an hour ago: tried again later."
      return 0
    fi
  fi
  owe "$opened" relabel "" "$head" - "the merge conflict of $head is gone"
}
# due_catchup: the catch-up of an outside pull request whose head no review, no hold comment and no run of
# this workflow names (no run met it), whose head repository is still there, and whose newest CI run of the
# head ended over an hour ago, with none still to finish: a catchup run, whose post job closes and reopens it
# with the OSS Verify App's token. GitHub then starts CI on the head, and the review of that CI run follows.
# A hold comment names its head whatever the age of the run that held it, which can be older than the 8 days
# of runs that this pass reads. Once for each head: the comment job of the run that closed and reopened the
# pull request records the head in the label comment (<!-- review-catchup <head> -->, caught), and that
# line stays there however long ago the run was. A pull request whose head repository is gone is never
# closed: GitHub cannot reopen it.
due_catchup() {
  [ "$review" = none ] && [ "$held" = false ] || return 0
  [ -z "$(runs_of '[a-z]+' "$head")" ] || return 0
  if [ "$caught" = true ]; then
    echo "#$number: its label comment records a catch-up of $head, which runs once for each head."
    return 0
  fi
  if [ "${pr_repo[$number]:-0}" = 0 ]; then
    echo "#$number: the head repository of $head is gone, so it is not closed."
    return 0
  fi
  ci_head || return 1
  ci_over || return 0
  owe "$ci" catchup "" "$head" - "no run met $head, and its CI run ended at $ci"
}
# rerun <run> <facts>: when the screen of <run> passed and its review job then failed at a step whose name
# starts with "Sign in" (its facts), the failed jobs of <run> run again (restart, which each step defines after
# its source line: the rescreen pass's calls rerun-failed-jobs, which its token's actions: write allows; the
# trust job's starts nothing): the screen's verdict stands and is paid once, and the review job's Count step
# counts the run once. Its caller asks only once the run ended over an hour ago, so a run runs again at most
# once an hour. It fails, and the caller starts a new run, for any other run, for a run made before kept
# (the artifact that its review job reads is gone, or goes before the re-run takes it), for a run at its
# attempt 51 (50 re-runs, which GitHub allows no more of), and when GitHub refuses the re-run, which stops
# nothing else of this run. Else taken holds the head for this run.
rerun() {
  local screen reviewed created attempt
  read -r _ screen _ _ _ reviewed _ <<< "$2"
  [ "$screen" = success ] && [ "$reviewed" = signin ] || return 1
  read -r created attempt <<< "$(awk -v r="$1" '$1 == r { print $2, $13; exit }' "$seen/runs")"
  if [[ ! ${created:-} > $kept ]]; then
    echo "#$number: run $1 was made at ${created:-no time GitHub gives}, before $kept: GitHub can delete" \
      "the data of its gather job before a re-run reads it. A new run instead."
    return 1
  fi
  if [[ ! ${attempt:-} =~ ^[1-9][0-9]*$ ]] || (( attempt > 50 )); then
    echo "#$number: run $1 is at attempt ${attempt:-none}, past 50 re-runs: a new run instead."
    return 1
  fi
  restart "$1" || return 1
  echo "#$number: the screen of run $1 passed and its review could not sign in: its failed jobs run again."
  taken=1
}
# due_old: the review of the head of an outside pull request whose review is in the form of before the move
# off pull_request_target, and none of now, under the CI conditions of the catch-up: a review run of that
# head, which reviews it from the API and closes and reopens nothing. Once for each head, and again an hour
# after each run of it that posted nothing of its own: one that ended at a failed sign-in (the failed jobs of
# that run when its screen passed and its review could not sign in, by rerun, else a new run), and one whose
# comment job failed or was cancelled (a GitHub error on the post, say, for which no hold job runs). After
# REVIEW_TRIES runs of the head whose comment job failed so, the head is not tried again (head_stopped). A
# hold that is tried again leaves it to that hold.
due_old() {
  local created ended run f signin commented last="" latest="" known="" tries=0
  [ "$review" = old ] && [ -z "$retaken" ] || return 0
  ci_head || return 1
  ci_over || return 0
  while read -r created ended run; do
    [ -n "${run:-}" ] || continue
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r signin _ _ _ _ _ commented _ <<< "$f"
    if [[ $commented == failure || $commented == cancelled ]]; then
      tries=$((tries + 1))
    elif [ "$signin" != signin ]; then
      echo "#$number: run $run took the review of $head."
      return 0
    fi
    last=$ended latest=$run known=$f
  done < <(runs_of review "$head" workflow_dispatch)
  if (( tries >= REVIEW_TRIES )); then
    head_stopped review "$tries"
    return 0
  fi
  if [ -n "$last" ] && [[ ! $last < $hour ]]; then
    echo "#$number: the review run of $head posted no review (a failed sign-in or a failed comment job), less" \
      "than an hour ago: tried again later."
    return 0
  fi
  if [ -n "$latest" ] && rerun "$latest" "$known"; then return 0; fi
  owe "$ci" review "$limited" "$head" - "the review of $head is in the form of before"
}
# due_unreviewed: the review of the head of an open pull request into main, a writer's too, that a run of
# this workflow names and that no review and no hold comment names, with no merge conflict and no CI run of
# the head still to finish (the review of an approval's CI run comes first). At the next run when each run
# that named the head stopped at its trust job, gave the task conflict, or was a relabel (a draft marked
# ready, a base changed to main, a conflict that went away); else once the newest of them ended over an hour
# ago, as for a run that could not sign in: the failed jobs of that run when its screen passed and its review
# could not sign in (rerun), else a new run. Not when the post job of that newest run failed: the App's retry
# takes it. A CI run that its trust job stopped reviewed nothing, and can be the run of another pull request
# of the head (one into another branch): it is never that newest run, so it holds back no re-run and no
# review. After REVIEW_TRIES workflow_dispatch review runs of the head that ended with no failed sign-in and gave
# no conflict, the head is not tried again (head_stopped). The review of an outsider's pull request counts on its
# author. The review of a writer's pull request counts on the account that started the newest CI run of the
# head (pusher), when that account has no write access and is not one of the APPS: the run's name then ends
# with " of <login>", and its trust job screens it first, on the limit of that account, as the trust job of
# that CI run's own event does.
due_unreviewed() {
  local list created ended run task event f signin post early all=true newest="" last="" tries=0
  local latest="" known="" met="" who=""
  [ -z "$retaken" ] || return 0
  list=$(awk -v n="$number" -v h="$head" '$7 == n && $9 == h { print $2, $3, $1, $8, $6 }' "$seen/runs" \
    | sort)
  [ -n "$list" ] || return 0
  head_of || return 1
  [ "$review" = none ] && [ "$held" = false ] || return 0
  if [ "$outsider" = false ]; then
    [ "$conflicted" = false ] || return 0
    merge_of || return 1
    if [ "$merge" = dirty ] || [ "$merge" = null ]; then
      echo "#$number: $head has a merge conflict, or GitHub has not computed whether it has one."
      return 0
    fi
  fi
  ci_head || return 1
  if [ "$ci" = pending ]; then
    echo "#$number: a CI run of $head has not finished, and its review comes after it."
    return 0
  fi
  while read -r created ended run task event; do
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r signin _ post _ early _ <<< "$f"
    [[ $early == stopped || $early == conflict || $task == relabel ]] || all=false
    if [[ $task == review && $event == workflow_dispatch && $signin != signin && $early != conflict ]]; then
      tries=$((tries + 1))
    fi
    met=$ended
    [[ $event == workflow_run && $early == stopped ]] || newest=$ended last=$post latest=$run known=$f
  done <<< "$list"
  if (( tries >= REVIEW_TRIES )); then
    head_stopped review "$tries"
    return 0
  fi
  if [ "$last" = signin ] || [ "$last" = failure ]; then
    echo "#$number: the post job of the newest run of $head failed: the App's retry takes it."
    return 0
  fi
  if [ "$all" = false ] && [[ ! $newest < $hour ]]; then
    echo "#$number: the newest run of $head ended at $newest with no review, less than an hour ago."
    return 0
  fi
  rerun "$latest" "$known" && return 0
  if [ "$outsider" = false ]; then
    who=$(pusher "$head" "${pr_repo[$number]:-0}" "${pr_ref[$number]:--}") \
      || { echo "::error::the CI runs of $head could not be read."; return 1; }
    if [ -n "$who" ]; then
      access_of "$who" || return 1
      (( ${access[$who]} != 0 )) || who=""
    fi
  fi
  owe "${newest:-$met}" review "${who:-$limited}" "$head" - "the runs of $head ended with no review"
}
# due_variable: the value of REPO_PAIRS_IMPORT_PATHS that the workflow recorded for the head of an outside
# pull request: the newer of the label comment's line <!-- repo-pairs-import-paths <head>: <value> --> and
# the same line in the output text of the head's check run repo-pairs/import-approved, by the OSS Verify App,
# of this pull request: a check run belongs to a commit, so only one whose external_id is <number>:<head>
# counts, and one of another pull request of the same commit does not. When it is not the value now
# (IMPORT_PATHS, none when empty), or the head has a review of now and neither line: a relabel, which decides
# R12 again by the value now and sets the label again. Once an hour.
due_variable() {
  local found checks at value same ended run
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  found=$(comments "$number" | SHA=$head jq -r 'select(.user.login == "github-actions[bot]"
      and ((.body // "") | startswith("<!-- review-label -->")))
    | .updated_at as $at | .body | split("\n")[]
    | capture("^<!-- repo-pairs-import-paths (?<h>[0-9a-f]{40}): (?<v>.*) -->$")
    | select(.h == $ENV.SHA) | "\($at) \(.v)"') \
    || { echo "::error::the comments of #$number could not be read."; return 1; }
  [ -n "$found" ] || [ "$review" = new ] || return 0
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  checks=$(SHA=$head NUMBER=$number gh api --method GET --paginate "repos/$REPO/commits/$head/check-runs" \
    -f check_name=repo-pairs/import-approved -F per_page=100 --jq '.check_runs[]
      | select(.name == "repo-pairs/import-approved" and .head_sha == $ENV.SHA
               and (.app.id | tostring) == $ENV.OSS_VERIFY_APP_ID
               and .external_id == "\($ENV.NUMBER):\($ENV.SHA)")
      | (.completed_at // .started_at // "-") as $at | .output.text // "" | split("\n")[]
      | capture("^<!-- repo-pairs-import-paths (?<h>[0-9a-f]{40}): (?<v>.*) -->$")
      | select(.h == $ENV.SHA) | "\($at) \(.v)"') \
    || { echo "::error::the check runs of $head could not be read."; return 1; }
  read -r at value <<< "$(printf '%s\n%s\n' "$found" "$checks" | awk NF | sort | tail -n 1)"
  if [ -n "${at:-}" ]; then
    same=$(jq -n --arg recorded "$value" --arg now "${IMPORT_PATHS:-}" \
      '($recorded | try fromjson catch {}) == (if $now == "" then null else $now end)') \
      || { echo "::error::the value recorded for $head could not be read."; return 1; }
    [ "$same" != true ] || return 0
  fi
  read -r _ ended run <<< "$(runs_of relabel "$head" workflow_dispatch | tail -n 1)"
  if [ -n "${run:-}" ] && [[ ! $ended < $hour ]]; then
    echo "#$number: relabel run $run of $head ended at $ended, less than an hour ago: tried again later."
    return 0
  fi
  owe "${at:-$opened}" relabel "" "$head" - \
    "the value of REPO_PAIRS_IMPORT_PATHS recorded for $head is not the value now"
}
# consider [<merge>]: the runs that #number is due, by each reason above (due_*), in order. A writer's pull
# request gets only the work that its holds name and the review of a head that a run left with no review. A
# read that fails for it leaves it for the next run, and this run fails at its end. Once a reason took the
# head (taken), no later one takes it in this run. hold is the newest hold of each work of the item (holds).
# <merge> is the mergeable_state of the pull request #number that a run of the pass with a number read
# (rescreen.yml). With it, consider gives only the work that such a run does, for an outside pull request
# alone: the conflict of its head when <merge> is dirty (due_conflict), else the approval of the runs of its
# head that GitHub holds (due_approve, after due_held for the hold of its approval alone).
# shellcheck disable=SC2120 # review.yml's trust job passes no argument, a run with a number passes one
consider() {
  local head="" outsider=false limited="" hold=""
  local retaken="" waits="" waits_read="" marks="" marks_read="" taken="" reason
  local review=none held=false conflicted=false caught=false steered=false head_read="" merge=${1:-} ci=""
  local ci_read="" withdraws="" because=""
  if [ "$draft" != false ]; then
    echo "#$number: a draft, of which the trust job takes no run."
    return 0
  fi
  if [ "$kind" = pr ]; then
    head=${pr_head[$number]:-}
    if [ -z "$head" ]; then
      echo "#$number: not in the list of open pull requests: left for the next run."
      return 0
    fi
    if [ "${pr_draft[$number]}" != false ]; then
      echo "#$number: a draft, of which the trust job takes no run."
      return 0
    fi
    if [ "${pr_base[$number]}" != main ]; then
      echo "#$number: into ${pr_base[$number]}, not main."
      return 0
    fi
  fi
  if [ -n "${running[$number]:-}" ]; then
    echo "#$number: a run of it has not finished."
    return 0
  fi
  access_of "$author" || return 1
  if (( ${access[$author]} != 0 )); then outsider=true limited=$author; fi
  [ "$labelled" = true ] || [ "$outsider" = true ] || [ "$kind" = pr ] || return 0
  if [ "$labelled" = true ] || [ "$outsider" = true ]; then
    hold=$(holds "$number") || { echo "::error::the comments of #$number could not be read."; return 1; }
  fi
  if (( $# > 0 )); then
    if [ "$outsider" = false ]; then
      echo "#$number: its author has write access, so a run of the pass with a number takes no work of it."
      return 0
    fi
    if [ "$merge" = dirty ]; then
      head_of || return 1
      due_conflict
      return
    fi
    if [ "$labelled" = true ]; then due_held approve || return 1; fi
    due_approve
    return
  fi
  if [ "$labelled" = true ]; then due_held || return 1; fi
  if [ "$outsider" = false ]; then
    [ "$kind" = pr ] || return 0
    due_unreviewed
    return
  fi
  due_answer || return 1
  if [ "$kind" = issue ]; then
    due_draft || return 1
    return 0
  fi
  due_approve || return 1
  [ -z "$taken" ] || return 0
  head_of || return 1
  due_conflict || return 1
  [ -z "$taken" ] || return 0
  # A hold that is not tried again names the head: of the App's writes of the head, only the withdrawal of its import
  # check run is tried again, and only while a relabel of the head withdraws it (relabel_withdraws): a screen held the
  # head after each review that screened it, the newest screened review of the head does not pass, or a review newer
  # than it gives a blocking finding or the verdict person. Such a relabel records no import check run. So the App's
  # retry (due_retry) still takes a run of the head whose post job failed: one relabel an hour after that run ended.
  # After REVIEW_TRIES failed tries, head_stopped import stops it, and the hold of that stop, which names the head,
  # ends the retry. While a relabel of the head can record an import check run, no App write of the head is tried
  # again.
  if [ -n "$(awk -v h="$head" '$3 == "-" && $9 == h' <<< "$hold")" ]; then
    if [ -z "$(awk -v h="$head" '$1 == "import" && $3 == "-" && $9 == h' <<< "$hold")" ]; then
      withdraws=$(relabel_withdraws "$number" "$head") \
        || { echo "::error::the comments of #$number could not be read."; return 1; }
      case $withdraws in
        screen) because="a screen held $head" ;;
        blocking) because="a review of $head asks for a change" ;;
        person) because="a review of $head has questions for Sami" ;;
      esac
      if [ -n "$because" ]; then
        echo "#$number: a hold that is not tried again names $head, and $because. So the rescreen pass tries again" \
          "only one App write of $head: the withdrawal of its import check run."
        due_retry 'review|rescreen|relabel|approve' relabel import
        return
      fi
    fi
    echo "#$number: a hold that is not tried again names $head: the App's writes of it are not tried again."
    return 0
  fi
  for reason in catchup old unreviewed variable; do
    "due_$reason" || return 1
    [ -z "$taken" ] || return 0
  done
  due_retry 'review|rescreen|relabel' relabel import || return 1
  [ -z "$taken" ] || return 0
  due_retry catchup catchup catchup || return 1
}
# consider_closed: a catch-up left closed, the one closed item that this pass takes: #number, a pull request
# of an outside author that is not merged, whose newest close (at and by, of the list of the closed pull
# requests) is the OSS Verify App's (OSS_VERIFY_APP_LOGIN) and falls between the start and the end of
# a catchup run of it whose post job failed or was cancelled (the closing run), as the trust job tells it
# (left_closed). Its workflow_dispatch runs are read back to the day before the close. It is due a catchup run,
# which only reopens it, once an hour after the newest catchup run of it ended. Each catchup run since the
# closing run counts, whatever its outcome, but one that failed at a sign-in: after REVIEW_TRIES of them it is
# not tried again (left_stopped), and nothing more of it is read (gave_up).
consider_closed() {
  local head="" given closing="" made="" created ended run started f post count=0 newest=""
  if [ -n "${running[$number]:-}" ]; then
    echo "#$number: a run of it has not finished."
    return 0
  fi
  access_of "$author" || return 1
  (( ${access[$author]} != 0 )) || return 0
  [ "${by:-}" = "$OSS_VERIFY_APP_LOGIN" ] || return 0
  [[ ${at:-} =~ ^[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z$ ]] || return 0
  given=$(gave_up "$number") || { echo "::error::the comments of #$number could not be read."; return 1; }
  if [ "$given" = true ]; then
    echo "#$number: the catch-up closed it and could not reopen it: Sami reopens it."
    return 0
  fi
  reach "$(date -u -d "${at:0:10} -1 day" +%Y-%m-%d)" || return 1
  while read -r created ended run started; do
    [[ ! $at < $started ]] || continue
    [ "$ended" = - ] || [[ ! $ended < $at ]] || continue
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r _ _ post _ <<< "$f"
    case $post in
      failure|signin|cancelled) closing=$run made=$created; break ;;
    esac
  done < <(awk -v n="$number" '$6 == "workflow_dispatch" && $7 == n && $8 == "catchup" {
    print $2, $3, $1, $12 }' "$seen/runs" | sort)
  [ -n "$closing" ] || return 0
  while read -r created ended run; do
    [[ ! $created < $made ]] || continue
    newest=$ended
    [ "$run" != "$closing" ] || continue
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    [ "${f%% *}" = signin ] || count=$((count + 1))
  done < <(runs_of catchup "" workflow_dispatch)
  head=$(gh api "repos/$REPO/pulls/$number" --jq .head.sha) \
    || { echo "::error::pull request #$number could not be read."; return 1; }
  [[ $head =~ ^[0-9a-f]{40}$ ]] || { echo "::error::pull request #$number names no head commit."; return 1; }
  if (( count >= REVIEW_TRIES )); then
    left_stopped "$count"
    return 0
  fi
  if [[ ! $newest < $hour ]]; then
    echo "#$number: catch-up run of it ended at $newest, less than an hour ago: tried again later."
    return 0
  fi
  owe "$at" catchup "" "$head" - "a catch-up closed it at $at and did not reopen it"
}
# item_row: the --jq filter of an item as the issues API gives it, which consider reads: "<number> <kind>
# <draft> <labelled> <opened> <author>", kind pr or issue, labelled true when it has HELD_LABEL, and opened
# the time when it was opened.
# shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
item_row='[.number, (if .pull_request then "pr" else "issue" end), (.draft // false),
  any(.labels[]?; .name == $ENV.HELD_LABEL), (.created_at // "-"), (.user.login // "")] | map(tostring)
  | join(" ")'
