# shellcheck shell=bash
# held.sh: the functions and values of the rescreen pass. Three steps source this file, each at one place of its script:
# - the step "Start the runs that the open items are due" of .github/workflows/rescreen.yml, the rescreen pass;
# - the trust job's step "Whether the author and the account that started the run have write access" of
#   .github/workflows/review.yml. With these functions, the trust job of each run that the pass starts reads again why
#   the pass started it;
# - the hold job's step "Label it and say that it was held" of review.yml, which reads try_rule, the one rule of what
#   counts as a try of a run, and calls replaced_hold, the one rule of each writer of a hold comment.
# Before each of the first two steps, its job checks out this file, trusted.sh and rules.py, the files beside it, alone,
# at the commit whose workflow file runs (github.sha, a commit of main). The hold job checks out main's .github/. So a
# file of main runs, and never a file of a pull request. relabel_withdraws, holds and replaced_hold run rules.py from
# that checkout ($GITHUB_WORKSPACE/.github/review/rules.py): the order of the words on a head is written once, in
# rules.py.
# Before the source line, each step sets seen, a directory that the step makes for itself. The first two steps also
# source trusted.sh, which defines the function trusted, before it, and define restart after it, which rerun calls.
# The functions and jq filters of the file read REPO, HELD_LABEL, REVIEW_TRIES and IMPORT_PATHS from the environment
# of the step, GITHUB_REPOSITORY_ID, which GitHub sets in each step, and RUN_ID, which the trust step alone sets. The
# source line sets values, defines functions, and makes $seen/due and $seen/stops empty. It reads nothing from GitHub.
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
# holds <number>: the newest hold comment of each work on <number>, one on each line: "<work> <time>
# <run> <tries> <kind> <task> <comment> <id> <head>". rules.py holds picks it, by the one model of the order
# of the words (OSSV-613's architect, round 30, item 1): a hold of the screen counts from the time when its
# run read the item (its marker <!-- review-held-read <time> -->), any other hold, or one with no such marker,
# from when GitHub last changed it (rules.py word_time), and of holds at the same time the later as GitHub
# lists them is the newest. Its work is the one of rules.py hold_work. <time> is when GitHub last
# changed it. For a hold that the rescreen pass tries again (its
# marker <!-- review-held-<kind> <run> <tries>[ <task>[ <comment>]] -->): <kind> is limit
# (OUTSIDE_HOURLY_LIMIT), cap (SCREENED_HOURLY_CAP) or transient (a screened review, answer or draft that
# failed or ran out of time, or a run whose gather or screen job failed), <run> the run of
# the event this hold comes from (a run that takes the hold
# again keeps it), <tries> the screened reviews of it that failed so far, <task> the task that takes it again
# (answer, draft or approve as the marker names it, and rescreen for a marker with no task), and <comment>
# the comment that a held answer answers (- for none). Each of <run> to <comment> is - for a hold that is not
# tried again (the screen held it, or its tries are used up). <id> is the id of the comment, and <head> the
# head that the hold names (- for none). Only github-actions[bot]'s comments count.
holds() {
  comments "$1" | python3 "$GITHUB_WORKSPACE/.github/review/rules.py" holds \
    | jq -r '(.body // "") as $b | "\(.work) \(.updated_at // "-") \(($b
        | capture("\n<!-- review-held-(?<kind>limit|cap|transient) (?<run>[0-9]+)(?: (?<tries>[0-9]+)(?: (?<task>answer|draft|approve)(?: (?<comment>[1-9][0-9]*))?)?)? -->(\n|$)")
        | "\(.run) \(.tries // "0") \(.kind) \(.task // "rescreen") \(.comment // "-")") // "- - - - -") \(
      .id) \(($b | capture("\n<!-- review-held-head (?<h>[0-9a-f]{40}) -->(\n|$)") | .h) // "-")"'
}
# limit_hold <number> <work>: the newest hold comment of <work> on <number> (holds), as "<time> <run> <tries>
# <kind> <task> <comment> <id> <head>". Nothing when <work> has no hold comment.
limit_hold() {
  local found
  found=$(holds "$1") || return 1
  awk -v w="$2" '$1 == w { sub(/^[^ ]+ /, ""); print }' <<< "$found"
}
# replaced_hold <number> <work> <screen> <head> [<started>]: the one rule of each writer of a hold comment: the hold job
# of this workflow, and halt (stopped, head_stopped, left_stopped, answer_stopped and draft_stopped), whose stop the
# comment job writes. The id of the hold comment of github-actions[bot] on <number> that a new hold of <work>
# (rules.py hold_work) replaces, or nothing: then the new hold posts a comment of its own. <screen> is true for a new
# hold of the screen, and <head> is the head that the new hold names (empty for none). A hold of the screen (its text
# holds "The automated screen held ", and it has no marker of a hold that is tried again) names the head that the
# screen held, or none on an issue. A relabel and a review by hand read it (rules.py verdict, relabel_withdraws). So
# only a new hold of the screen that names the same head (or none, as it does) replaces it. A hold of the screen of
# another head posts a comment of its own, and so does each hold of another kind. Each other hold of <work> is replaced
# by any new hold of <work>. Of the holds of <work> that the new hold may replace, it replaces the newest by the one
# model of the order of the words (rules.py replaced-hold; OSSV-613's architect, round 30, item 1): a hold of the screen
# counts from the time when its run read the item (its marker <!-- review-held-read <time> -->), any other hold, or
# one with no such marker, from when GitHub last changed it (rules.py word_time), and of holds at the same time the
# later as GitHub lists them is the newest. A hold of other work stays as it is. <started> is the time when the trust
# job of the run of a new hold of the screen read the item (the hold job gives it; halt gives none). Such a hold never
# replaces a hold of a run that read the item later (OSSV-221's architect, 2026-11-24 16:19Z, F4, by A3 of 09:43Z): a
# hold that counts from a time after <started>, the time of its marker <!-- review-held-read <time> --> for a hold of
# the screen that has one, else when GitHub last changed it (rules.py word_time). So an older answer of an issue, which
# names no head and reads no newer word first, never takes the place of the hold of a newer answer, and a re-run
# attempt of the hold job, whose first hold names the same <started> (a hold of the screen names it on a pull request
# and on an issue), edits that hold in place. On a pull request, the hold job gives way to such a hold of the screen of
# the head before this (rules.py newer-word). Before either writer writes, it checks that <head> is still the head of
# the pull request (rules.py hold-head): a hold of an older head is stale, and writes no hold comment and changes no
# label.
replaced_hold() {
  comments "$1" | python3 "$GITHUB_WORKSPACE/.github/review/rules.py" replaced-hold "$2" "$3" "${4:--}" "${5:--}"
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
# under .github/, or 3,000 files or more, so the post job approves no run of it, and Sami approves its runs.
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
# the OSS Verify App, so the post job approved no run of it, and Sami approves its runs.
no_key_of() {
  # shellcheck disable=SC2016 # $ENV is jq's, read from this step's environment
  comments "$1" | SHA=$2 jq -rs 'any(.[]; .user.login == "github-actions[bot]" and ((.body // "")
    | startswith("<!-- review-label -->") and test("\n<!-- review-no-key " + $ENV.SHA + " -->(\n|$)")))'
}
# relabel_withdraws <number> <head>: why a relabel of <head> withdraws the import check run of <head>, from the
# comments of <number> and the import check runs of <head>, by the rule that the post job of that relabel reads
# (rules.py verdict, its why): rules.py relabel-withdraws, which orders the words on <head> by the one model of rules.py
# (word_key, outranks; OSSV-221's architect, 2026-11-24 14:29Z to 14:40Z). rules.py reads those check runs as that
# post job does (import_checks: every check run of <head>, filter=all, of the OSS Verify App, for this pull request,
# external_id <number>:<head>): a refused review posts no comment, so only its check run or its line gives its word
# (OSSV-613's architect, round 30, item 1). Each review comment and each hold comment of the screen counts from the
# time when its run read the item (rules.py word_time), a check run from the time that its summary names, and at the
# same time a verdict or a hold outranks a pass. screen when a hold of the screen of <head> (its hold comment, or a
# check run for the reason screen) outranks each review comment of <head> whose run screened it: the state held. Else
# "<why> owed" while a label comment holds the line <!-- withdraw-owed <head> <why> <run> <read> -->
# of a withdrawal that a run owes (it found a reason for it and did not finish it, or no comment gives that reason
# yet), and the newest review comment of <head> whose run screened it does not outrank that line: the line is a word
# from <read> (rules.py owed_reason; OSSV-221's architect, 2026-11-25 01:13Z, G1), whatever the newest review says
# else. Only a run that finished the withdrawal of <head> takes that line out, and only while a comment of
# github-actions[bot] gives a reason for it (rules.py owed, line_reason). Else blocking, person or refused, of the
# newest word of <head> that gives one (a review comment, or a check run of not-approved for that reason) when the
# newest screened review comment of <head> does not outrank it. Else -: then a relabel of <head> withdraws nothing. It
# records an import check run only when the newest review comment of <head> holds the marker
# <!-- review-screened <head> --> and passes, with no withdraw-owed line of <head>, and no withdrawal of the newest
# read among the import check runs of <head> blocks it (rules.py verdict, screened, and withdrawal_stands). It fails
# when GitHub could not give the comments or the check runs: gh's error, or rules.py's for the check runs, says which.
relabel_withdraws() {
  comments "$1" > /dev/null || return 1
  python3 "$GITHUB_WORKSPACE/.github/review/rules.py" relabel-withdraws "$1" "$2" "$seen/comments-$1"
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
# exported <repository> <branch>: true for an export pull request: its head repository, whose id is <repository>, is
# this repository (GITHUB_REPOSITORY_ID), and its head branch <branch> starts with release/. The export opens such pull
# requests into main. Neither this workflow nor the rescreen pass acts on one (OSSV-221's architect, 2026-11-22
# 17:18Z): the trust job gives it no task on any event and for any task (review.yml, export_stop), and the rescreen
# pass starts no run of it (consider and consider_closed). A fork's branch with such a name does not make an export
# pull request: the head repository decides.
exported() {
  [[ -n ${GITHUB_REPOSITORY_ID:-} && $1 == "$GITHUB_REPOSITORY_ID" && $2 == release/* ]]
}
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
# <started> <attempt> <actor> <name>", - for none (ended, for a run that is not completed); attempt is its
# run_attempt, 1 for its first, and actor the login of the account that started it.
row='def row: "\(.id) \(.created_at // "-") \(if .status == "completed"
  then (.updated_at // .created_at // "-") else "-" end) \(.status // "-") \(.conclusion // "-") \(.event) \(
  .run_started_at // .created_at // "-") \(.run_attempt // 1) \(.actor.login // "-" | gsub("\\s"; "-")) \(
  .display_title // "" | gsub("[\r\n]"; " "))";'
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
# <status> <conclusion> <event> <number> <task> <head> <comment> <account> <started> <attempt> <actor>", - for none. A
# name gives its task and its item (run-name): #<n> ends at a space or at the end of the name, so that #12 is
# never #123, and a workflow_run's name gives its head, which the open pull requests into main map to the
# pull request into main with that head (pr_of), or, when more than one into main has it, to the one that the
# run's trust job names (reviewed). The comment of a stop's name is the stop. An item with a run that has not
# finished, of any task, gets no run (running). The run of this step (RUN_ID, the run of a stop whose trust
# job decides it again) is not one of them.
take() {
  local id created ended status conclusion event started attempt actor title number task head comment account
  local numbers
  local named='^(review|answer|draft|reply|rescreen|approve|catchup|conflict|relabel|stop) #([1-9][0-9]*)( at ([0-9a-f]{40}))?( for ([1-9][0-9]*|[a-z-]+))?( of ([A-Za-z0-9-]+(\[bot\])?))?$'
  local pushed='^review ([0-9a-f]{40}) by '
  local opened='^review #([1-9][0-9]*)$'
  local answered='^answer #([1-9][0-9]*) for ([1-9][0-9]*) by '
  while read -r id created ended status conclusion event started attempt actor title; do
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
        "${attempt:--} ${actor:--}" >> "$seen/runs"
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
# try_rule: the start of a jq filter that defines tried, the one rule of whether a run counts as a try of its work (D19
# and R10). facts reads it for each run that the functions below read, and the hold job reads it for its own run. Its
# input is the jobs of one attempt of a run, an array as GitHub lists them. judges_nothing gives the name of each failed
# step that signs in before the run judges anything of the item. These steps are each step whose name starts with
# "Sign in" in the screen job, the review job's step "Sign in to Anthropic", which comes before any model, and the post
# job's "Sign in as the OSS Verify App to approve". The review job's two sign-ins of the fresh reader come after the
# model ran, and the second of them comes after the verdict. So a failure of either counts a try, and the post job
# withdraws for a verdict that the review gave before it failed (OSSV-221's architect, 2026-11-22 06:23Z). This departs
# from plan D19, which named "Sign in to Anthropic for the fresh reader" as a step that counts no try. tried gives the
# first word of these that applies:
# - signin when such a step failed: the run judged nothing of the item, and counts no try;
# - limit when the trust job stopped the run at OUTSIDE_HOURLY_LIMIT: after the trust job, only the hold job ran, and
#   each other job (at least one) was skipped. The run counts no try;
# - cap when the review job's step "Hold at the hourly cap" failed: the run stopped at the hourly cap of the reviews,
#   before the model ran, and counts no try. The limit and the cap bound the retries of such runs;
# - stopped when the trust job succeeded and decided that the run has no task: each job after it (at least one) was
#   skipped, the hold job too. The run tried nothing, and counts no try. A trust job that failed or was skipped counts
#   a try (OSSV-221's architect, 2026-11-22 13:57Z and 14:00Z). Each reader takes a stop of the trust job from this
#   word alone, and such a run of the pass can settle its name (settles);
# - running while a job of the run has not finished: the run counts no try yet;
# - try for every other outcome. These include a failure of the post job's "Sign in as the OSS Verify App", the sign-in
#   for the App's writes of the import check run and of a catch-up, and a failure of a sign-in of the fresh reader. They
#   also include a job that failed or was cancelled, and an outcome that this rule does not name.
# shellcheck disable=SC2016 # $job, $t and $others are jq's
try_rule='def judges_nothing: .[] | (.name // "") as $job | .steps[]?
    | select(.conclusion == "failure"
             and ((($job | test("^screen( |$)")) and ((.name // "") | startswith("Sign in")))
                  or (($job | test("^review( |$)")) and .name == "Sign in to Anthropic")
                  or ($job == "post" and .name == "Sign in as the OSS Verify App to approve")))
    | .name;
  def tried: (map(select(.name == "trust")) | first) as $t
    | map(select(.name != "trust" and .name != "rescreen" and .name != "hold")) as $others
    | map(select(.name != "trust" and .name != "rescreen")) as $after
    | if any(judges_nothing; true) then "signin"
      elif ($t.conclusion // "") == "success" and any(.[]; .name == "hold" and .conclusion != "skipped")
           and ($others | length) > 0 and all($others[]; .conclusion == "skipped") then "limit"
      elif any(.[] | select((.name // "") | test("^review( |$)")) | .steps[]?;
               .name == "Hold at the hourly cap" and .conclusion == "failure") then "cap"
      elif ($t.conclusion // "") == "success" and ($after | length) > 0 and all($after[]; .conclusion == "skipped")
      then "stopped"
      elif any(.[]; .status | IN("queued", "in_progress", "waiting", "requested", "pending")) then "running"
      else "try" end; '
# facts <run>: what the jobs of <run> show, read once: "<tried> <screen> <post> <settled> <early> <reviewed>
# <commented> <held> <posted> <answered> <trust> <counts>", - for none. tried: whether the run counts a try of its
# work, as the one rule of every reader gives it (try_rule): signin, limit, cap, stopped, running or try. screen: the
# conclusion of its screen job. post: the conclusion of its post job, signin for one that failed at a step whose name
# starts with "Sign in" and failure for one that failed at another (a write of the App, say). settled: its post job
# approved held runs or recorded the import check run. early: stopped when no job ran after its trust job (the trust
# job was skipped, or every job after it was, whatever the trust job's result), conflict when the comment job alone ran
# after it (the task conflict). early tells the readers that ask whether a run did any work after its trust job
# (due_retry, due_conflict, due_unreviewed). No reader counts a try or settles a name by it: tried does that, and a run
# whose trust job failed counts a try. reviewed: signin when its review job failed at a step whose name starts with
# "Sign in". commented: the conclusion of its comment job, which posts the review, the answer or the label comment of a
# draft (success when it did, failure or cancelled when it posted nothing or not all), or left when that job left its
# answer to a later run (its step of that name ran): another run answered a comment of that answer first, so it posted
# nothing of its own. held: held when its hold job ran, so the run itself posted nothing. posted and answered: the
# conclusions of the comment job's steps "Post the review, or replace the one posted before" and "Post the answer". A
# review or an answer that the fresh reader refused skips its step, and its comment job still succeeds. trust: the
# conclusion of its trust job, which failures reads. counts, the last field, which the rescreen pass reads (pace): count
# when the run counts toward the limit of the account that its name ends with, as the trust job's earlier counts it
# (not a run that its trust job refused, nor one whose screen could not sign in; a run whose screen passed and whose
# review then could not sign in counts, once: its screen ran, and its failed jobs run again with no new screen), else
# skip. The job rescreen, which review.yml had before this pass moved to rescreen.yml and which each of its runs
# skipped, is none of the run's jobs.
facts() {
  local file=$seen/jobs-$1
  jobs_of "$1" || return 1
  jq -rs "$try_rule"'def signed_out:
      any(.steps[]?; ((.name // "") | startswith("Sign in")) and .conclusion == "failure");
    (map(select(.name == "trust")) | first) as $t | (map(select(.name == "post")) | first) as $p
    | map(select(.name != "trust" and .name != "rescreen")) as $rest
    | [tried,
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
       ((map(select(.name == "comment")) | first) as $c
        | ("Post the review, or replace the one posted before", "Post the answer") as $n
        | ([$c.steps[]? | select(.name == $n) | .conclusion] | first) // "-"),
       ($t.conclusion // "-"),
       (if $t == null then "count" elif $t.conclusion == "skipped" then "skip"
        elif $t.status == "completed" and ($rest | length) > 0 and ($rest | all(.conclusion == "skipped"))
        then "skip"
        elif any($rest[] | select(.name | test("^screen( |$)")); signed_out) then "skip"
        else "count" end)] | join(" ")' "$file"
}
# settles <run> <tried> <task>: whether <run>, whose tried (facts) is <tried>, settles its name: a run of the pass
# (workflow_dispatch, started by github-actions[bot]) of <task> (approve, draft, answer, rescreen or review) that its
# trust job stopped (tried stopped) as it decided that the name of <run> has no task. The pass then starts no run of
# that name again until a new head, comment or hold gives a new name (OSSV-221's architect, 2026-11-22 14:00Z and
# 14:14Z). For a review, due_unreviewed asks this of the newest run of the head alone, so a newer run of the head ends
# the settle. Not a run of an event, nor a run that a person or an App started by hand with the same name (its actor
# is not github-actions[bot]), nor a duplicate: a run older than <run>, of its event and name, that had not finished
# when <run> was made, so that the trust job of <run> can have stopped it for that run, as it stops a second approval
# run of a head.
settles() {
  [ "$2" = stopped ] || return 1
  awk -v r="$1" -v t="$3" 'NR == FNR {
      if ($1 == r) { e = $6; w = $8; k = $7 " " $8 " " $9 " " $10 " " $11; m = $2; a = $14 }
      next }
    $1 + 0 < r + 0 && $6 == e && $7 " " $8 " " $9 " " $10 " " $11 == k && $2 <= m && ($3 == "-" || $3 > m) { d = 1 }
    END { exit !(e == "workflow_dispatch" && a == "github-actions[bot]" && w == t && !d) }' "$seen/runs" "$seen/runs"
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
# stop_note: the sentences of the error line of stopped, head_stopped, left_stopped, answer_stopped and draft_stopped
# that say what the run of the stop writes.
stop_note="A run of the task stop writes its hold comment, unless a newer comment or a newer head of the item stops"
stop_note+=" that run first. It writes the label comment of the stop when GitHub said whether the author has write"
stop_note+=" access."
# halt <stop> <fact> <work> <title> <text>: the work of #number is not tried again, at a bound of its tries
# (stopped, head_stopped, left_stopped, answer_stopped and draft_stopped). The rescreen pass writes nothing for it: it
# starts a run of review.yml with the task stop, named "stop #<n>[ at <head>] for <stop>", at most one for each item in
# each of its runs. The trust job of that run decides the stop again with these functions, and gives its
# comment job the stop as halt wrote it to $seen/stops: the state label of <fact> (tries_used_up, or
# left_closed for a catch-up left closed), with Sami's next step in the label comment, then the hold comment
# with <title> and <text>, which names the head of a pull request and holds no marker of a hold that is tried
# again. It is no hold of the screen: its text never holds "The automated screen held ". It goes in the place of
# the hold comment of <work> (rules.py hold_work) that replaced_hold picks for it, or as a new one: never in the place
# of a hold of other work, nor of a hold of the screen. The run of the pass fails for it. The head of the stop is the
# current head that this step read (read_pulls, or consider_closed for a closed pull request). The comment job's
# step reads the head again before it writes, and writes nothing for a stale stop (rules.py hold-head).
halt() {
  local line at id
  failed=1
  line=$(limit_hold "$number" "$3") || { echo "::error::the comments of #$number could not be read."; return 1; }
  read -r at _ <<< "$line"
  id=$(replaced_hold "$number" "$3" false "${head:-}") \
    || { echo "::error::the comments of #$number could not be read."; return 1; }
  jq -nc --arg stop "$1" --arg fact "$2" --arg id "${id:-}" --arg title "$4" --arg text "$5" \
    --arg head "${head:-}" '{stop: $stop, fact: $fact, id: $id, title: $title, text: $text, head: $head}' \
    >> "$seen/stops"
  owe "${at:-$hour}" stop "" "${head:-}" "$1" "its work is not tried again"
}
# stopped <task> <tries> [<run> <how>]: the work of the hold that held_work read is not tried again, after <tries>
# tries: runs of <task> since the hold, or since <run>, the newest run that settled the hold, that settled nothing
# (halt, with the stop hold-<work>). <how> is finished when the comment job of <run> posted (its review, its answer,
# or the label comment of its draft or of its approval); refused when the fresh reader refused the review or the
# answer of <run>, so that its comment job succeeded and posted neither; else started: the post job of <run>
# approved held runs or recorded the import check run, and its comment job posted nothing. waits-on-theorem, with the
# label comment's step "Sami starts again, by hand, the work that the hold comment names", and a hold comment that
# says so in the place of that hold, the newest of its work, which is no hold of the screen (replaced_hold). With
# <run>, that comment says what that try did (finished the work, stopped it, started the checks, or recorded the check
# repo-pairs/import-approved on the head) before the tries that did not finish. The hold comment of other work stays
# as it is.
stopped() {
  local title work what tried began of=$1 runs=$1 from="since its hold at $h_at"
  [ "$of" != rescreen ] || of=review runs="rescreen or review"
  [ -z "${3:-}" ] || from="after run $3, which settled its hold"
  echo "::error::#$number: $from, $2 runs of $runs were tries that settled nothing, with no new hold. The work" \
    "of the hold is not tried again. $stop_note"
  case $1 in
    answer) title="Automated answer held." work="the automated answer" ;;
    draft) title="Automated reply held." work="the automated reply" ;;
    approve) title="Automated start of the checks held." work="" ;;
    *) title="Automated review held." work="the automated review" ;;
  esac
  what="this issue"
  [ "$kind" != pr ] || what="this pull request"
  if [ -n "$work" ] && [ -z "${3:-}" ]; then
    tried="The workflow tried $work again $2 times after it held $what, and none of these tries finished."
  elif [ -n "$work" ]; then
    began="finished $work"
    case ${4:-} in
      started) began="recorded the check \`repo-pairs/import-approved\` on its head commit" ;;
      refused) began="stopped $work, so the workflow did not post it" ;;
    esac
    tried="The workflow held $what, and a later try $began. After that, the workflow tried $work again"
    tried+=" $2 times, and none of these tries finished."
  elif [ -z "${3:-}" ]; then
    tried="The workflow held the start of the checks of $what. Then it tried $2 times to start them, and no try"
    tried+=" finished."
  else
    began="Then a later try started them."
    [ "${4:-}" = started ] || began="Then a later try finished without starting them."
    tried="The workflow held the start of the checks of $what. $began After that, the workflow tried $2 more times"
    tried+=" to start checks of $what, and no try finished."
  fi
  halt "hold-$of" tries_used_up "$of" "$title" "$tried The workflow does not try it again. You do not need to do anything."
}
# head_stopped <work> <tries>: the automated <work> (review; approval, of the held runs; import, the import
# check; or catchup) of the head of #number did not finish after <tries> tries, and is not tried again (halt,
# with the stop head-<work>): waits-on-theorem, with the label comment's step "Sami starts again, by hand, the
# work that the hold comment names", then a hold comment that says so and names the head, in the place of the
# newest hold comment of that work (rules.py hold_work) that is not a hold of the screen (replaced_hold), or as a new
# one. It never takes the place of a hold of other work, which the rescreen pass still takes again, nor of a hold of the
# screen, which a relabel and a review by hand read. That hold stops each later try of the head, and no other reason
# takes the head in this run (taken).
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
  echo "::error::#$number at $head: $text It is not tried again. $stop_note"
  halt "head-$of" tries_used_up "$of" "$title" "$text The workflow does not try it again."
}
# left_stopped <tries>: the catch-up that closed #number could not reopen it after <tries> runs that only
# reopen it, and is not tried again (halt, with the stop reopen): waits-on-theorem, with the label comment's
# step "Sami reopens the pull request", then a hold comment that says so, in the place of the newest hold
# comment of a catch-up (replaced_hold), or as a new one. That comment ends each later read of the item's runs
# (gave_up).
left_stopped() {
  echo "::error::#$number: the automated catch-up closed it and could not reopen it after $1 tries: it is not" \
    "tried again. $stop_note"
  halt reopen left_closed catchup "Automated close and reopen held." \
    "The workflow closed this pull request so that GitHub starts its checks. It could not reopen the pull request after $1 tries."
}
# failures <tasks>: of the runs of the head of #number of a task of <tasks>, newest first, back to the newest
# whose post job succeeded, how many count a try (tried, of facts) and had a post job that ran and did not succeed, or
# a trust job that failed or was cancelled. Such a post job failed at a write of the App or at a sign-in, or was
# cancelled, or ended in a way that this does not name. A failed "Sign in as the OSS Verify App to approve" counts no
# try (R10), and a failed "Sign in as the OSS Verify App" counts one. A run whose trust job failed or was cancelled
# (its conclusion failure or cancelled) counts for every task, so that the App's retry stops also when the trust jobs
# of its relabels keep failing (OSSV-221's architect, 2026-11-22 16:06Z). A trust job that runs past its
# timeout-minutes ends cancelled, and each job after it is skipped. Such a run counts as one whose trust job failed
# (OSSV-221's architect, 2026-11-22 04:30Z and 2026-11-23 01:37Z). For the approval (<tasks> approve), each run that
# counts a try counts, also a run whose post job did not run for another cause: its screen job ran out of time, say,
# or its screen job and its hold job failed. A run that its trust job stopped (tried stopped) counts for no task: it
# tried nothing. A run of the pass with a number and a run with none can each start an approval run of one head, and
# the trust job stops the later one. At most REVIEW_TRIES: each counts a try of the head.
failures() {
  local n=0 run f tried post trust
  while read -r _ _ run; do
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read." >&2; return 1; }
    read -r tried _ post _ _ _ _ _ _ _ trust _ <<< "$f"
    [ "$post" != success ] || break
    if [ "$tried" = try ] && { [ "$1" = approve ] || [ "$trust" = failure ] || [ "$trust" = cancelled ] \
      || { [ "$post" != - ] && [ "$post" != skipped ]; }; }; then
      n=$((n + 1))
    fi
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
# the hold, after the newest run that settled it, is a try that settled nothing (a review's hold is taken again
# as a rescreen, and counts the rescreens and the reviews), but a run that counts no try (tried, of facts): a
# sign-in that judges nothing failed in it (D19), OUTSIDE_HOURLY_LIMIT or the hourly cap stopped it before any work,
# or its trust job decided that it has no task. Then the work is taken again. A run that settled the hold is no try: so
# a held run made after an approval gets REVIEW_TRIES tries of its own. After REVIEW_TRIES tries (stopped), or while
# the newest run of its task is under an hour old, it is not started. Nor when the newest run of its task since the
# hold is a run of the pass that its trust job stopped as the task had no work (settles): that settles the hold until
# a new hold.
# retaken holds the task of each hold that this takes, which the other reasons leave to it.
held_work() {
  local task=$h_task pattern since tries=0 newest="" created run latest="" f who from
  local tried="" settled="" early="" commented="" ended="" settler="" how="" posted="" answered=""
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
  # Each run of the task since the hold, oldest first: the facts of the newest stay. A run that settled the hold
  # ends the count of the runs before it (how: finished when its comment job posted, refused when the fresh reader
  # refused its review or its answer, so that the step that posts it was skipped, else started, as its post job
  # approved held runs or recorded the import check run), and each later run counts a try when the one rule says so
  # (tried).
  while read -r created _ run; do
    [ -n "${run:-}" ] || continue
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r tried _ _ settled early _ commented _ posted answered _ <<< "$f"
    newest=$created latest=$run ended=""
    if [ "$settled" = settled ] || { [ "$commented" = success ] && [ "$early" = - ]; }; then
      ended=1 settler=$run tries=0 how=started
      if [ "$commented" = success ] && [ "$early" = - ]; then
        how=finished
        case $task in
          rescreen) [ "$posted" != skipped ] || how=refused ;;
          answer) [ "$answered" != skipped ] || how=refused ;;
        esac
      fi
    elif [ "$tried" = try ]; then
      tries=$((tries + 1))
    fi
  done <<< "$since"
  if [ -n "$ended" ]; then
    echo "#$number: run $latest of $task approved the held runs, recorded the import check or posted, so" \
      "its hold is settled."
    retaken=${retaken%" $task"}
    return 0
  fi
  if (( tries >= REVIEW_TRIES )); then
    stopped "$task" "$tries" "$settler" "$how"
    return
  fi
  if [ -n "$latest" ] && settles "$latest" "$tried" "$task"; then
    echo "#$number: the trust job of run $latest of $task found no work for it and stopped it. That settles its hold" \
      "until a new hold."
    return 0
  fi
  if [ -n "$latest" ]; then
    # Spaced as the hold's own hour is, so that a short outage of GitHub does not use up the tries.
    if [[ ! $newest < $hour ]]; then
      echo "#$number: $task ran at $newest, less than an hour ago, with no new hold: tried again later."
      return 0
    fi
    from="since its hold"
    [ -z "$settler" ] || from="after run $settler, which settled its hold,"
    if (( tries > 0 )); then
      echo "#$number: $tries runs of $task $from settled nothing; trying again."
    else
      echo "#$number: no run of $task $from counts a try. Each one had a failed sign-in, the limit, the cap or a stop" \
        "of its trust job. The rescreen pass tries again."
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
# answer_stopped <comment> <tries>: <tries> answer runs of <comment> counted a try and posted nothing of their own, with
# no hold (due_answer), so its answer is not tried again (halt, with the stop answer-post): waits-on-theorem, with the
# label comment's step "Sami starts again, by hand, the work that the hold comment names", then a hold comment that
# says so, in the place of the newest hold comment of an answer that is not a hold of the screen (replaced_hold), or as
# a new one. That hold is not tried again, so the comments before it wait for no answer (waiting).
answer_stopped() {
  local what="this issue"
  [ "$kind" != pr ] || what="this pull request"
  echo "::error::#$number: $2 answer runs of comment $1 counted a try and posted nothing: the answer is not tried" \
    "again. $stop_note"
  halt answer-post tries_used_up answer "Automated answer held." "The workflow tried the automated answer to your comment on $what $2 times, and none of these tries posted it. The workflow does not try it again. You do not need to do anything."
}
# due_answer: the answer to the newest comment of the author of #number that waits for one (waiting) and is
# over 15 minutes old, on an issue only after its first reply posted. The newest run that names the comment,
# of its own event (issue_comment) or of workflow_dispatch, took it when its comment job succeeded. A run of the pass
# that its trust job stopped as the comment had no work (settles) settles the comment: a new comment gives a new name.
# Another run that its trust job stopped (tried stopped: the run of the comment's own event, or a duplicate), or one
# that left its answer to a later run (another run answered a comment of it first), took nothing, and the comment is
# due at once. Any other run posted nothing of its own: a sign-in that judges nothing failed in it (tried, of facts),
# its trust job failed, its hold job held it, its comment job failed or was cancelled (a GitHub error on the post, say,
# for which no hold job runs), or its comment job did not run and no hold job held it (its screen job ran out of time,
# say). Then the comment is due once an hour after that run ended. Such a run that counts a try and that no hold job
# held changes no label, so the item can keep waits-on-author over the comment. Each such run of the comment counts:
# after REVIEW_TRIES of them, the answer is not tried again (answer_stopped). A hold of an answer that is tried again
# leaves the comments to that hold (due_held), which counts its tries.
due_answer() {
  local at id runs created ended run r f tried commented held tries=0
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
    read -r tried _ _ _ _ _ commented _ <<< "$f"
    if [ "$commented" = success ]; then
      echo "#$number: run $run took comment $id."
      return 0
    fi
    if settles "$run" "$tried" answer; then
      echo "#$number: the trust job of run $run of comment $id found no work for it and stopped it. That settles" \
        "comment $id."
      return 0
    fi
    if [ "$tried" != stopped ] && [ "$commented" != left ]; then
      while read -r _ _ r; do
        f=$(facts "$r") || { echo "::error::the jobs of run $r could not be read."; return 1; }
        read -r tried _ _ _ _ _ commented held _ <<< "$f"
        if [[ $tried == try && $commented != success && $commented != left && $held != held ]]; then
          tries=$((tries + 1))
        fi
      done <<< "$runs"
      if (( tries >= REVIEW_TRIES )); then
        answer_stopped "$id" "$tries"
        return 0
      fi
      if [[ ! $ended < $hour ]]; then
        echo "#$number: run $run of comment $id posted nothing of its own (a failed sign-in, a hold, or a job that" \
          "failed, was cancelled or did not run), less than an hour ago: tried again later."
        return 0
      fi
    fi
  fi
  owe "$at" answer "$limited" - "$id" "comment $id of $author waits for an answer"
}
# draft_stopped <tries>: <tries> draft runs of #number counted a try and stored no draft, with no hold (due_draft), so
# its draft is not tried again (halt, with the stop hold-draft): waits-on-theorem, with the label comment's step "Sami
# starts again, by hand, the work that the hold comment names", then a hold comment that says so, in the place of the
# newest hold comment of a draft that is not a hold of the screen (replaced_hold), or as a new one. No hold of the draft
# came before, so the text does not say that the workflow held the issue.
draft_stopped() {
  echo "::error::#$number: $1 draft runs counted a try and stored no draft, with no hold: the draft is not tried" \
    "again. $stop_note"
  halt hold-draft tries_used_up draft "Automated reply held." "The workflow tried the automated reply $1 times, and none of these tries finished. The workflow does not try it again. You do not need to do anything."
}
# due_draft: the draft of the reply to an outside issue whose label comment holds neither a stored draft nor
# a posted reply, once an hour after its newest draft run (of its issues event, by hand or of the pass) ended.
# Not after a hold that is not tried again (the issue waits on Sami), and not while a hold is tried again
# (due_held takes it). Each draft run of the issue that counts a try (tried, of facts) counts: it stored no draft, as
# the label comment holds none, and no hold of the draft is there. After REVIEW_TRIES of them, the draft is not tried
# again (draft_stopped). A draft run that its trust job stopped counts no try. When the newest draft run is a run of
# the pass that its trust job stopped as the draft had no work (settles), that settles the draft until a hold.
due_draft() {
  local last run f tried="" newest="" tries=0
  marks_of || return 1
  [ -z "$marks" ] || return 0
  if [ -n "$(awk '$3 == "-"' <<< "$hold")" ]; then
    echo "#$number: its hold is not tried again, so its draft waits on Sami."
    return 0
  fi
  [ -z "$retaken" ] || return 0
  # Each draft run of the issue, oldest first: the tried of the newest stays.
  while read -r _ run; do
    [ -n "${run:-}" ] || continue
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    tried=${f%% *} newest=$run
    [ "$tried" != try ] || tries=$((tries + 1))
  done <<< "$(awk -v n="$number" '$7 == n && (($6 == "workflow_dispatch" && $8 == "draft") || $6 == "issues") {
    print $2, $1 }' "$seen/runs" | sort)"
  if (( tries >= REVIEW_TRIES )); then
    draft_stopped "$tries"
    return 0
  fi
  if [ -n "$newest" ] && settles "$newest" "$tried" draft; then
    echo "#$number: the trust job of draft run $newest found no work for it and stopped it. That settles the draft" \
      "until a hold."
    return 0
  fi
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
# held run: its screen job passed and its post job neither failed nor was cancelled (by the App's retry, such a post
# job leaves no verdict), or a hold that is not tried again, the newest of its work, names the head. Once an hour after
# the newest approval run of the head. When that run, made after the newest held run, is a run of the pass that its
# trust job stopped as the head had no work (settles), that settles the head until a newer held run. When that run
# counts a try (tried, of facts), or its trust job stopped it for an earlier run, the approval runs of the head that
# count a try count the tries of the head (failures): a failed "Sign in as the OSS Verify App to approve" counts none
# (R10), nor does a run that its trust job stopped, and a failed "Sign in as the OSS Verify App", a failed write of the
# App, a cancelled post job, or a post job that did not run (the screen job ran out of time, or the trust job failed,
# say) counts one. After REVIEW_TRIES of them, the head is not tried again (head_stopped): waits-on-theorem, with Sami's
# next step. A hold of an approval that is tried again leaves it to that hold (due_held). Never for a head that the
# label comment records as one whose runs the workflow does not approve (a file under .github/, or 3,000 files or
# more; head_marks, steered), or as one that the screen passed while the environment post held no key of the OSS
# Verify App (no_key_of): the post job approved no run of such a head.
due_approve() {
  local list n last created ended run f tried screen post tries keyless
  held_of || { echo "::error::the runs of $head could not be read."; return 1; }
  list=$(held_at "$head" "${pr_repo[$number]:-0}" "${pr_ref[$number]:--}") \
    || { echo "::error::the runs of $head could not be read."; return 1; }
  n=$(grep -c . <<< "$list" || true)
  (( n > 0 )) || return 0
  last=$(sort <<< "$list" | tail -n 1)
  [[ $retaken != *" approve"* ]] || return 0
  head_of || return 1
  if [ "$steered" = true ]; then
    echo "#$number: its label comment records that the pull request at $head changes a file under .github/, or it" \
      "changes 3,000 files or more. The workflow does not approve the runs of $head, so Sami approves them."
    return 0
  fi
  keyless=$(no_key_of "$number" "$head") || { echo "::error::the comments of #$number could not be read."; return 1; }
  if [ "$keyless" = true ]; then
    echo "#$number: its label comment records that a run screened $head while the environment post had no key of the" \
      "OSS Verify App. So Sami approves the runs of $head."
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
      read -r tried screen post _ <<< "$f"
      if [ "$screen" = success ] && [ "$post" != failure ] && [ "$post" != signin ] && [ "$post" != cancelled ]; then
        echo "#$number: run $run screened $head with a verdict."
        return 0
      fi
      if settles "$run" "$tried" approve; then
        echo "#$number: the trust job of approval run $run of $head found no work for it and stopped it. That settles" \
          "$head until a newer held run."
        return 0
      fi
      if [ "$tried" = try ] || [ "$tried" = stopped ]; then
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
# unrecorded <run>: whether, in the newest attempt of <run> ($seen/jobs-<run>, which facts read), its comment job failed
# or was cancelled before it recorded what the run owes (OSSV-613's architect, 2026-11-27 00:24Z, choice (a)): at
# GitHub's own first step of a job ("Set up job"), at its checkout ("Run actions/checkout"), or at either step that
# records a withdrawal, "Record a withdrawal that the post job owes" or "Record the withdrawal of a refused review whose
# post job did not finish" (review.yml, the comment job), which come first after the checkout. The pass cannot read the
# verdict of a job, so it reads the steps of that job: the step that failed or was cancelled, the first one, and each
# step before it are all among those steps. A comment job that GitHub ended before its first step (it lists no step)
# died there too. Such a job wrote no line <!-- withdraw-owed <head> <why> <run> <read> --> and posted no review
# comment, whatever the verdict of the run's review: pass, blocking, person, or refused, which posts no comment and
# whose word only that line or a check run of the post job carries. When the post job of the run failed or was
# cancelled too, it can have written the check run or the withdrawal before it failed, or neither. Either way, while
# the newest attempt of the run recorded nothing, the run gets the re-run of its failed jobs (due_rerun) and no relabel
# (due_retry, due_variable). A comment job that failed at a later step (its label step, say) recorded what it owes.
unrecorded() {
  [ "$(jq -rs 'any(.[] | select(.name == "comment" and (.conclusion == "failure" or .conclusion == "cancelled"));
      [.steps[]?] | (map(.conclusion == "failure" or .conclusion == "cancelled") | index(true)) as $died
      | .[:(if $died == null then length else $died + 1 end)]
      | all((.name // "") as $n | $n == "Set up job" or ($n | test("^Run actions/checkout(@|$)"))
          or $n == "Record a withdrawal that the post job owes"
          or $n == "Record the withdrawal of a refused review whose post job did not finish"))' \
    "$seen/jobs-$1")" = true ]
}
# unrecorded_run: the id of the newest run, by when GitHub made it, of the reviews, rescreens, relabels and approvals
# of the head of #number whose post job did not succeed and whose comment job recorded nothing that the run owes
# (unrecorded), or nothing for none. It fails when the jobs of a run could not be read.
unrecorded_run() {
  local id f post
  while read -r _ _ id; do
    f=$(facts "$id") || { echo "::error::the jobs of run $id could not be read." >&2; return 1; }
    read -r _ _ post _ <<< "$f"
    [ "$post" != success ] && [ "$post" != skipped ] || continue
    if unrecorded "$id"; then
      echo "$id"
      return 0
    fi
  done < <(runs_of 'review|rescreen|relabel|approve' "$head" | sort -r)
}
# due_retry <tasks> <task> <work>: the App's retry. When the post job of the newest run of the head of #number
# of a task of <tasks> failed, at a sign-in or at a write of the App, or was cancelled (it ran out of time, say), the
# head is due <task> again. A CI run that did nothing after its trust job (early, of facts) is not that newest run: it
# posted nothing, and it can be the run of another pull request of the head (one into another branch). For the task
# relabel, a run of the pass that did nothing after its trust job is not that newest run either: a relabel that its
# trust job stopped (GitHub had not computed the merge state yet, say), or whose trust job failed or was cancelled,
# wrote nothing, so it ends no retry of a withdrawal that GitHub refused (ruling 2 of OSSV-221's architect, 2026-11-20
# 07:33Z). When the post job of that newest run succeeded, an older run that did work and whose post job failed or was
# cancelled is due the retry all the same, while no run of <task> did work after it: the post job of a run that GitHub
# made later can have run before the older run's post job failed, so it did not do the older run's work (the failure
# sweep of test_orders.py, OSSV-613's architect, 2026-11-26 02:25Z). The retry comes once an hour after the end of the
# newest run of the pass among the runs read here, or after the end of the newest run that did work when it is a CI
# run and no run of the pass came after it. When the run due the retry counts a try (tried, of facts), or a run passed
# over to reach the newest run that did work had a trust job that failed or was cancelled, the runs of the head whose
# post job did not succeed count the tries of the head (failures): a failed "Sign in as the OSS Verify App to approve"
# counts none (R10), and a failed "Sign in as the OSS Verify App", a failed write of the App or a cancelled post job
# counts one. So does a run whose trust job failed or was cancelled (it ran out of time, say), but not one that its
# trust job stopped (OSSV-221's architect, 2026-11-22 16:06Z and 2026-11-23 01:37Z). After REVIEW_TRIES of them, the
# automated <work> of the head is not tried again (head_stopped <work>). A run whose post job failed or was cancelled and
# whose comment job failed or was cancelled before it recorded what the run owes (unrecorded: at its checkout, or at
# either step that records a withdrawal, whatever the verdict) is no run of the retry: while the newest attempt of that
# run recorded nothing, the retry starts nothing for it, at any time (OSSV-613's architect, 2026-11-27 00:24Z, choice
# (a)). The pass runs the failed jobs of that run again (due_rerun), the post job too, an hour after it ended, and at
# REVIEW_TRIES attempts it starts the stop of the import check of the head (head_stopped import), whose hold ends this
# retry of the head (consider).
due_retry() {
  local created ended run event task f tried post early trust tries how=failed last="" latest="" untrusted=""
  local top="" top_run="" found=""
  # The runs of the head, newest first: to the newest one that did work after its trust job (top, when it ended, and
  # top_run, its id), and, when its post job did not fail, on to an older run that did work and whose post job failed,
  # before a run of <task> that did work. last: when the newest run of the pass among them ended (latest). untrusted: a
  # run passed over to reach top whose trust job failed or was cancelled (it ran out of time, say), which counts a try.
  while read -r created ended run event task; do
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r tried _ post _ early _ _ _ _ _ trust _ <<< "$f"
    if [ "$event" != workflow_run ] && [ -z "$last" ]; then last=$ended latest=$run; fi
    if [ -z "$top" ]; then
      if [ "$early" = stopped ] && { [ "$event" = workflow_run ] || [ "$2" = relabel ]; }; then
        if [ "$trust" = failure ] || [ "$trust" = cancelled ]; then untrusted=1; fi
        continue
      fi
      top=$ended top_run=$run
    elif [ "$early" = stopped ]; then
      continue
    fi
    if [ "$post" = signin ] || [ "$post" = failure ] || [ "$post" = cancelled ]; then
      if unrecorded "$run"; then
        echo "#$number: the post job of run $run did not succeed, and its comment job failed or was cancelled before" \
          "it recorded what the run owes. The App's retry starts no relabel for run $run."
        return 0
      fi
      found=1
      break
    fi
    [ "$task" != "$2" ] || return 0
  done < <(awk -v n="$number" -v re="^($1)\$" -v h="$head" '$7 == n && $8 ~ re && $9 == h {
    print $2, $3, $1, $6, $8 }' "$seen/runs" | sort -r)
  [ -n "$found" ] || return 0
  [ "$post" != cancelled ] || how="was cancelled"
  # The hour counts from the end of latest, or, with no run of the pass among the runs read here (latest is empty: each
  # of them is a CI review), from the end of top_run, which can be a newer run than run.
  if [[ ! ${last:-$top} < $hour ]]; then
    if [ -n "$latest" ] && [ "$latest" != "$run" ]; then
      echo "#$number: the post job of run $run $how. Run $latest of $head ended less than an hour ago. The rescreen" \
        "pass tries again later."
    elif [ -z "$latest" ]; then
      echo "#$number: the post job of run $run $how. Run $top_run of $head, the newest review run of that head that" \
        "did work, ended less than an hour ago: tried again later."
    else
      echo "#$number: the post job of run $run $how, and that run ended less than an hour ago: tried again later."
    fi
    return 0
  fi
  if [ "$tried" = try ] || [ -n "$untrusted" ]; then
    tries=$(failures "$1") || return 1
    if (( tries >= REVIEW_TRIES )); then
      head_stopped "$3" "$tries"
      return 0
    fi
  fi
  owe "$ended" "$2" "" "$head" - "the post job of run $run $how"
}
# unclaimed <run>: whether, in the newest attempt of <run> ($seen/jobs-<run>, which facts read), the last step of each
# comment job and hold job that failed or was cancelled succeeded: "Leave no label that says the workflow recorded the
# check" (rules.py unclaim), which GitHub runs after a step of its job failed or was cancelled. A step that failed, was
# cancelled or did not run did not succeed, and neither did a step of a list of jobs that jq cannot read.
unclaimed() {
  [ "$(jq -rs 'all(.[] | select((.name == "comment" or .name == "hold")
      and (.conclusion == "failure" or .conclusion == "cancelled"));
    any(.steps[]?; .name == "Leave no label that says the workflow recorded the check" and .conclusion == "success"))' \
    "$seen/jobs-$1")" = true ]
}
# due_rerun: the comment job or the hold job of a run of #number failed or was cancelled, while its post job succeeded
# or was skipped (OSSV-613's architect, 2026-11-25 23:02Z, item 3b). The run is the newest such run, by when GitHub
# made it, of the reviews, rescreens, relabels and approvals of the head and of the answers of #number (the name of an
# answer gives no head) that did work after their trust jobs: a run that its trust job stopped did none. A newer run
# that wrote all it owed does not hide it: a run that GitHub made earlier can read the item later, so its word can be
# the newest one, and the step of its failed job that skips its posts gives way when it is not (rules.py newer-word).
# That run wrote only a part of what it owed on the item (a review comment, a hold comment, a label, a label comment).
# Its last step, when it succeeds, leaves no label comment that says that the workflow recorded the check while no such
# check run stands (rules.py unclaim). Once it ended an hour or more ago, its failed jobs run again (restart, as rerun
# does): the post job of that run does not run again. The App's retry takes a run whose post job failed or was
# cancelled (due_retry), but for a run whose comment job failed or was cancelled before it recorded what the run owes
# (unrecorded: at its checkout, or at either step that records a withdrawal, whatever the verdict of its review, which
# the pass cannot read). Such a run wrote neither its review comment nor the line of a withdrawal that it owes. Its
# post job can have written its check run or its withdrawal before it failed, or neither. This takes it too: the failed
# jobs of that run run again, the post job among them (its withdrawal or its check run) and the comment job (the line,
# or the review comment), each bound the same, and the App's retry (due_retry) and the relabel of a new value of
# REPO_PAIRS_IMPORT_PATHS (due_variable) give way to it (OSSV-613's architect, 2026-11-27 00:24Z, choice (a)).
# Until an hour after it ended, this waits, and those two give way, so that none starts a run for the head (v). But
# under the stop of the import check of the head (a hold of the work import that is not tried again names the head),
# this takes no such run: its post job again would be an App write of the head, which could record the check, and that
# stop ends each App write of the head; its label comment names Sami's step. A run whose post job succeeded or was
# skipped still runs its failed jobs again under that stop (item 3b).
# A re-run is one more attempt of the run (its run_attempt, the column 13 of $seen/runs). It starts only while that
# attempt is below REVIEW_TRIES, and the log gives the number of the attempt that starts. At REVIEW_TRIES attempts the
# failed jobs do not run again, and the log gives the count. Then unclaimed gives whether the last step of each comment
# job and hold job of the run that failed or was cancelled, "Leave no label that says the workflow recorded the check"
# (rules.py unclaim), succeeded in the newest attempt (OSSV-613's architect, round 30, item 2). When it did, the label
# comment holds no such claim, and the work is not tried again (head_stopped: review for a review or a rescreen,
# approval for an approval, import for a relabel), unless a hold that is not tried again names the head already (a
# hold of the screen, or the stop of an earlier pass), and but for an answer, whose comment the pass answers again by
# itself (due_answer). But a run that recorded nothing that it owes (unrecorded), of an outside author's pull request,
# gets the stop of the import check of the head (head_stopped import), whatever its last step did, as its comment job
# never reached its label step: the label comment of that stop names Sami's step, and its hold ends the App's retry of
# the head (consider calls no due_retry under it), so that no relabel records the check over the word that the run did
# not record, until a newer run of the head reads the item. Once that stop names the head, this takes the run no more
# (above). A writer's run, which no App's retry takes, gets the bound of its work below as any run. When the last step
# did not succeed (it failed, was cancelled or did not run: GitHub refused its read of the label comments on each try,
# say), the label comment of an outside author's pull request can still say that the workflow recorded the check while
# no such check run stands (the state import is for such a pull request alone, rules.py label_state), and no
# job of the run writes again. Then, in this order:
# - a stop of the head that GitHub made after the run ended: nothing more. Its comment job writes the label comment of
#   that stop when GitHub said whether the author has write access, so each run gets at most one stop;
# - a hold that is not tried again, of the work import, names the head (the stop of the import check of the head):
#   for any task, the stop of the import check again (head_stopped import), which takes the place of that hold
#   (replaced_hold) and makes no write of the App. A relabel's post job could write a check run of the head, which
#   that stop ends;
# - a relabel, and a review, a rescreen or an approval with no hold that is not tried again and names the head: the
#   stop of its work (head_stopped: import for a relabel, review for a review or a rescreen, approval for an approval);
# - an answer, and a review, a rescreen or an approval while another hold that is not tried again names the head (a
#   hold of the screen, say): nothing more when a relabel of the head that GitHub made after the run ended did work
#   after its trust job, as the label comment is that relabel's to set. When the comment job or the hold job of that
#   relabel failed, this takes that relabel, and when its post job failed, the App's retry does (due_retry). After
#   REVIEW_TRIES such relabels that did nothing after their trust jobs (a trust job stopped its run, as no review, hold
#   comment or merge conflict of the workflow names the head, say, or failed or was cancelled), the stop of the import
#   check (head_stopped import). Else one relabel of the head
#   in this pass: its label step writes the label comment from what the workflow wrote of the head when GitHub said
#   whether the author has write access, and by R12 that comment says that the workflow recorded the check only while
#   a check run with the conclusion success and the marker line of the head stands.
# consider calls this for no issue, and the label comment of an issue never says that the workflow recorded the check:
# the state import is for a pull request of an outside author alone (rules.py label_state). When GitHub refuses the
# re-run, nothing is taken and no run starts in its place: the next pass tries the re-run again. A head that this pass
# already starts a run for, or whose hold the pass tries again (retaken), gets no re-run: that run takes its place.
due_rerun() {
  local created ended id task f post early commented hold_job run="" which="" how="" attempt work
  local stood what made relabel stop idle owes="" import_stop line
  [ -z "$retaken" ] || return 0
  if awk -v n="$number" '$2 == n { found = 1 } END { exit !found }' "$seen/due"; then return 0; fi
  # The stop of the import check of the head: a hold of the work import that is not tried again names it (holds).
  import_stop=$(awk -v h="$head" '$1 == "import" && $3 == "-" && $9 == h' <<< "$hold")
  while read -r created ended id task; do
    f=$(facts "$id") || { echo "::error::the jobs of run $id could not be read."; return 1; }
    read -r _ _ post _ early _ commented _ <<< "$f"
    [ "$early" != stopped ] || continue
    owes=""
    if [ "$post" != success ] && [ "$post" != skipped ]; then
      unrecorded "$id" || continue
      if [ -n "$import_stop" ]; then
        echo "#$number: the post job of run $id did not succeed, and its comment job recorded nothing that the run" \
          "owes. The stop of the import check, a hold that is not tried again, names $head. So the failed jobs of run" \
          "$id, whose post job could record the check, do not run again. The label comment of that stop names Sami's" \
          "step when GitHub said whether the author has write access."
        continue
      fi
      owes=1
    fi
    hold_job=$(jq -rs 'map(select(.name == "hold")) | first | .conclusion // "-"' "$seen/jobs-$id")
    if [ "$commented" = failure ] || [ "$commented" = cancelled ]; then
      which=comment how=$commented
    elif [ "$hold_job" = failure ] || [ "$hold_job" = cancelled ]; then
      which=hold how=$hold_job
    else
      continue
    fi
    run=$id
    break
  done < <(awk -v n="$number" -v h="$head" '$7 == n && ($8 == "answer" ||
    ($9 == h && $8 ~ /^(review|rescreen|relabel|approve)$/)) { print $2, $3, $1, $8 }' "$seen/runs" | sort -r)
  [ -n "$run" ] || return 0
  [ "$how" != failure ] || how=failed
  [ "$how" != cancelled ] || how="was cancelled"
  if [ -n "$owes" ]; then
    echo "#$number: the post job of run $run did not succeed, and its comment job $how before it recorded what" \
      "the run owes."
  fi
  if [[ ! $ended < $hour ]]; then
    echo "#$number: the $which job of run $run $how, less than an hour ago: tried again later."
    return 0
  fi
  read -r attempt <<< "$(awk -v r="$run" '$1 == r { print $13; exit }' "$seen/runs")"
  if [[ ! ${attempt:-} =~ ^[1-9][0-9]*$ ]]; then
    echo "#$number: the $which job of run $run $how, and GitHub gives no attempt of that run: its failed jobs do not" \
      "run again."
    return 0
  fi
  case $task in
    approve) work=approval ;;
    relabel) work=import ;;
    answer) work="" ;;
    *) work=review ;;
  esac
  if (( attempt >= REVIEW_TRIES )); then
    echo "#$number: the $which job of run $run $how. That run is at attempt $attempt of $REVIEW_TRIES: its failed" \
      "jobs do not run again."
    # The work of each hold that is not tried again and names the head (holds).
    stood=$(awk -v h="$head" '$3 == "-" && $9 == h { print $1 }' <<< "$hold")
    if [ -n "$owes" ] && [ "$outsider" = true ]; then
      echo "#$number: the rescreen pass starts the stop of the import check of $head, whose hold ends the App's retry" \
        "of $head."
      head_stopped import "$attempt"
      return 0
    fi
    if unclaimed "$run"; then
      [ -n "$work" ] || return 0
      [ -z "$stood" ] || return 0
      head_stopped "$work" "$attempt"
      return 0
    fi
    line="#$number: in run $run, the step \"Leave no label that says the workflow recorded the check\" of a job that"
    line+=" failed or was cancelled did not succeed."
    # Only the label comment of an outside author's pull request can say that the workflow recorded the check: the
    # state import is for such a pull request alone (rules.py label_state).
    if [ "$outsider" = true ]; then
      line+=" So the label comment can still say that the workflow recorded the check repo-pairs/import-approved while"
      line+=" no such check run stands."
    fi
    echo "$line"
    # The newest stop of the head that GitHub made after the run ended: its comment job writes the label comment of
    # that stop when GitHub said whether the author has write access, so one stop is enough for each run.
    stop=$(runs_of stop "$head" | awk -v e="$ended" '$1 > e { s = $3 } END { print s }')
    if [ -n "$stop" ]; then
      echo "#$number: stop run $stop of $head was made after run $run ended, so the rescreen pass starts nothing more" \
        "for run $run."
      return 0
    fi
    if [ -n "$import_stop" ]; then
      echo "#$number: the stop of the import check, a hold that is not tried again, names $head. So the rescreen pass" \
        "starts no relabel, whose post job could write a check run of $head. It starts the stop of the import check" \
        "of $head again."
      head_stopped import "$attempt"
      return 0
    fi
    if [ "$task" = relabel ] || { [ -n "$work" ] && [ -z "$stood" ]; }; then
      what=$work
      [ "$work" != import ] || what="import check"
      echo "#$number: the rescreen pass starts the stop of the automated $what of $head."
      head_stopped "$work" "$attempt"
      return 0
    fi
    # The relabels of the head that GitHub made after the run ended: one that did work after its trust job sets the
    # label comment. idle counts those that did nothing after their trust jobs.
    idle=0
    while read -r made _ relabel; do
      [[ $made > $ended ]] || continue
      f=$(facts "$relabel") || { echo "::error::the jobs of run $relabel could not be read."; return 1; }
      read -r _ _ _ _ early _ <<< "$f"
      if [ "$early" = stopped ]; then idle=$((idle + 1)); continue; fi
      echo "#$number: relabel run $relabel of $head was made after run $run ended, and did work after its trust job." \
        "The rescreen pass leaves the label comment to that relabel, and starts nothing more for run $run."
      return 0
    done < <(runs_of relabel "$head")
    if (( idle >= REVIEW_TRIES )); then
      echo "#$number: each relabel of $head made after run $run ended did nothing after its trust job" \
        "($idle of them), so the rescreen pass starts no more relabels. It starts the stop of the import check of" \
        "$head."
      head_stopped import "$attempt"
      return 0
    fi
    what="run $run is an answer"
    [ -z "$work" ] || what="a hold that is not tried again names $head already"
    echo "#$number: $what, so the rescreen pass starts one relabel of $head. Its label step writes the label comment" \
      "from what the workflow wrote of $head, when GitHub said whether the author has write access. That label" \
      "comment says that the workflow recorded the check only while a check run repo-pairs/import-approved of" \
      "$head with the conclusion success stands."
    if (( idle > 0 )); then
      echo "#$number: each relabel of $head made after run $run ended did nothing after its trust job" \
        "($idle of them). After $REVIEW_TRIES such relabels, the rescreen pass starts the stop of the import check" \
        "of $head instead."
    fi
    what="the step \"Leave no label that says the workflow recorded the check\" of run $run did not succeed"
    # Only the label comment of an outside author's pull request can say that the workflow recorded the check.
    if [ "$outsider" = true ]; then
      what+=", so the label comment can still say that the workflow recorded the check repo-pairs/import-approved"
    fi
    owe "$ended" relabel "" "$head" - "$what"
    taken=1
    return 0
  fi
  restart "$run" || { echo "#$number: the next rescreen pass tries the failed jobs of run $run again."; return 0; }
  echo "#$number: the $which job of run $run $how. Its failed jobs run again: try $((attempt + 1)) of $REVIEW_TRIES."
  taken=1
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
  restart "$1" || { echo "#$number: a new run instead."; return 1; }
  echo "#$number: the screen of run $1 passed and its review could not sign in: its failed jobs run again."
  taken=1
}
# due_old: the review of the head of an outside pull request whose review is in the form of before the move
# off pull_request_target, and none of now, under the CI conditions of the catch-up: a review run of that
# head, which reviews it from the API and closes and reopens nothing. Once for each head, and again an hour
# after each run of it that posted nothing of its own: one in which a sign-in that judges nothing failed (tried, of
# facts; the failed jobs of that run when its screen passed and its review could not sign in, by rerun, else a new
# run), and one whose comment job failed or was cancelled (a GitHub error on the post, say, for which no hold job
# runs). After REVIEW_TRIES runs of the head whose comment job failed so, the head is not tried again (head_stopped).
# A hold that is tried again leaves it to that hold.
due_old() {
  local created ended run f tried commented last="" latest="" known="" tries=0
  [ "$review" = old ] && [ -z "$retaken" ] || return 0
  ci_head || return 1
  ci_over || return 0
  while read -r created ended run; do
    [ -n "${run:-}" ] || continue
    f=$(facts "$run") || { echo "::error::the jobs of run $run could not be read."; return 1; }
    read -r tried _ _ _ _ _ commented _ <<< "$f"
    if [[ $commented == failure || $commented == cancelled ]]; then
      tries=$((tries + 1))
    elif [ "$tried" != signin ]; then
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
# due_unreviewed: the review of the head of an open pull request into main, a writer's too, that a run of this workflow
# names and that no review and no hold comment names, with no merge conflict and no CI run of the head still to finish
# (the review of an approval's CI run comes first). At the next run when each run that named the head stopped at its
# trust job, gave the task conflict, or was a relabel (a draft marked ready, a base changed to main, a conflict that
# went away); else once the newest of them ended over an hour ago, as for a run that could not sign in: the failed jobs
# of that run when its screen passed and its review could not sign in (rerun), else a new run. Not when the post job of
# that newest run of an outsider's pull request failed or was cancelled: the App's retry takes it (due_retry, or
# due_approve for an approval). The pass tries no App write of a writer's pull request again, so for a writer such a run
# is due as any other. A CI run that its trust job stopped reviewed nothing, and can be the run of another pull request
# of the head (one into another branch): it is never that newest run, so it holds back no re-run and no review. After
# REVIEW_TRIES workflow_dispatch review runs of the head that count a try (tried, of facts) and gave no conflict, the
# head is not tried again (head_stopped). When the newest run of the head, but a CI run that its trust job stopped, is a
# review run of the pass that its trust job stopped as it found no task (settles), that run settles the review of the
# head: the pass starts no review of the head until a newer run of it (OSSV-221's architect, 2026-11-22 14:14Z and
# 19:42Z). The review of an outsider's pull request counts on its author. The review of a writer's pull request counts
# on the account that started the newest CI run of the head (pusher), when that account has no write access and is not
# one of the APPS: the run's name then ends with " of <login>", and its trust job screens it first, on the limit of
# that account, as the trust job of that CI run's own event does.
due_unreviewed() {
  local list created ended run task event f tried post early all=true newest="" last="" tries=0
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
    read -r tried _ post _ early _ <<< "$f"
    [[ $early == stopped || $early == conflict || $task == relabel ]] || all=false
    if [[ $task == review && $event == workflow_dispatch && $tried == try && $early != conflict ]]; then
      tries=$((tries + 1))
    fi
    met=$ended
    [[ $event == workflow_run && $early == stopped ]] || newest=$ended last=$post latest=$run known=$f
  done <<< "$list"
  if (( tries >= REVIEW_TRIES )); then
    head_stopped review "$tries"
    return 0
  fi
  if [ -n "$latest" ] && settles "$latest" "${known%% *}" review; then
    echo "#$number: the trust job of review run $latest of $head found no work for it and stopped it. That settles" \
      "the review of $head until a newer run of $head. A newer CI run of $head that did no work after its trust job" \
      "does not end the settle."
    return 0
  fi
  if [ "$outsider" = true ] && { [ "$last" = signin ] || [ "$last" = failure ] || [ "$last" = cancelled ]; }; then
    echo "#$number: the post job of the newest run of $head failed or was cancelled: the App's retry takes it."
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
# counts, and one of another pull request of the same commit does not. The read asks for every check run of
# the head (filter=all): by default GitHub lists only the newest of each name. When it is not the value now
# (IMPORT_PATHS, none when empty), or the head has a review of now and neither line: a relabel, which decides
# R12 again by the value now and sets the label again. Once an hour. But while a run of the head whose post job did not
# succeed recorded nothing that it owes (unrecorded_run), this gives way as the App's retry does (due_retry), and
# starts no relabel of the head. due_rerun runs the failed jobs of that run again an hour after it ended, or at
# REVIEW_TRIES attempts starts the stop of the import check of the head, under whose hold consider calls this no more
# (OSSV-613's architect, 2026-11-27 00:24Z, choice (a), (v)).
due_variable() {
  local found checks at value same ended run owing why
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
    -f check_name=repo-pairs/import-approved -f filter=all -F per_page=100 --jq '.check_runs[]
      | select(.name == "repo-pairs/import-approved" and .head_sha == $ENV.SHA
               and (.app.id | tostring) == $ENV.OSS_VERIFY_APP_ID
               and .external_id == "\($ENV.NUMBER):\($ENV.SHA)")
      | (.completed_at // .started_at // "-") as $at | .output.text // "" | split("\n")[]
      | capture("^<!-- repo-pairs-import-paths (?<h>[0-9a-f]{40}): (?<v>.*) -->$")
      | select(.h == $ENV.SHA) | "\($at) \(.v)"') \
    || { echo "::error::the check runs of $head could not be read."; return 1; }
  read -r at value <<< "$(printf '%s\n%s\n' "$found" "$checks" | awk NF | sort | tail -n 1)"
  # why: the reason of the relabel, from at. No value is recorded (the head has a review of now and neither line), or
  # the recorded value is not the value now.
  why="no value of REPO_PAIRS_IMPORT_PATHS is recorded for $head"
  if [ -n "${at:-}" ]; then
    same=$(jq -n --arg recorded "$value" --arg now "${IMPORT_PATHS:-}" \
      '($recorded | try fromjson catch {}) == (if $now == "" then null else $now end)') \
      || { echo "::error::the value recorded for $head could not be read."; return 1; }
    [ "$same" != true ] || return 0
    why="the value of REPO_PAIRS_IMPORT_PATHS recorded for $head is not the value now"
  fi
  owing=$(unrecorded_run) || return 1
  if [ -n "$owing" ]; then
    echo "#$number: $why. But the post job of run $owing did not succeed, and its comment job recorded nothing that" \
      "the run owes. This pass starts no relabel of $head for the value."
    return 0
  fi
  read -r _ ended run <<< "$(runs_of relabel "$head" workflow_dispatch | tail -n 1)"
  if [ -n "${run:-}" ] && [[ ! $ended < $hour ]]; then
    echo "#$number: relabel run $run of $head ended at $ended, less than an hour ago: tried again later."
    return 0
  fi
  owe "${at:-$opened}" relabel "" "$head" - "$why"
}
# consider [<merge>]: the runs that #number is due, by each reason above (due_*), in order. An export pull request
# (exported) is due none. A writer's pull request gets only the work that its holds name, the review of a head that a
# run left with no review, and the re-run of a comment job or a hold job that failed (due_rerun). A read that fails for
# it leaves it for the next run, and this run fails at its end. Once a reason took the head (taken), no later one takes
# it in this run. hold is the newest hold of each work of the item (holds).
# <merge> is the mergeable_state of the pull request #number that a run of the pass with a number read
# (rescreen.yml). With it, consider gives only the work that such a run does, for an outside pull request
# alone: the conflict of its head when <merge> is dirty (due_conflict), else the approval of the runs of its
# head that GitHub holds (due_approve, after due_held for the hold of its approval alone).
# shellcheck disable=SC2120 # review.yml's trust job passes no argument, a run with a number passes one
consider() {
  local head="" outsider=false limited="" hold=""
  local retaken="" waits="" waits_read="" marks="" marks_read="" taken="" reason
  local review=none held=false conflicted=false caught=false steered=false head_read="" merge=${1:-} ci=""
  local ci_read="" withdraws="" because="" from="" said=""
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
    if exported "${pr_repo[$number]:-0}" "${pr_ref[$number]:--}"; then
      echo "#$number: an export pull request, from the branch ${pr_ref[$number]} of this repository, of which the" \
        "trust job takes no run."
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
    due_unreviewed || return 1
    [ -z "$taken" ] || return 0
    due_rerun
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
  # A hold that is not tried again names the head: of the App's writes of the head, the withdrawal of its import check
  # run is tried again while a relabel of the head withdraws it (relabel_withdraws): a screen held the head after each
  # review that screened it, a label comment holds the line
  # <!-- withdraw-owed <head> <why> <run> <read> --> of a withdrawal that a run owes and no newer screened review of
  # the head outranks it, the newest screened review of the head does not pass, or a review newer than it
  # gives a blocking finding or the verdict person. Such a relabel records no import check run. So the App's retry
  # (due_retry) still takes a run of the head whose post job failed or was cancelled: one relabel an hour after that run
  # ended. After REVIEW_TRIES such tries (a relabel whose trust job failed among them), head_stopped import stops it,
  # and the hold of that stop, which names the head, ends the retry. When relabel_withdraws gives no reason to
  # withdraw (a newer screened review that passes outranks a hold of the screen, say), the App's retry takes a review,
  # a rescreen or a relabel all the same, as for any head (an approval's failures end at the stop of the approval): its
  # relabel decides by R12, so that the label comment ends true for its case (OSSV-613's architect, 2026-11-26 07:36Z,
  # C1 of the failure sweep). A hold of the stop of the import (head_stopped import) ends each App write of the head. A
  # comment job or a hold job that failed or was cancelled still runs again (due_rerun), when the App's retry takes no
  # run. Of the App's writes, such a re-run makes only those of a hold job (a withdrawal, and the check run that says
  # that the head is not approved for the import), and those of the post job of a run whose post job did not succeed and
  # whose comment job recorded nothing that it owes (unrecorded), but never under the stop of the import: due_rerun
  # takes no such run under it. The App's retry and the relabel of a new value of REPO_PAIRS_IMPORT_PATHS
  # (due_variable) give way to such a run: due_rerun runs its failed jobs again, the post job too, and at REVIEW_TRIES
  # attempts starts the stop of the import check, under whose hold this calls neither, so that no relabel of the head
  # follows (OSSV-613's architect, 2026-11-27 00:24Z, choice (a)).
  if [ -n "$(awk -v h="$head" '$3 == "-" && $9 == h' <<< "$hold")" ]; then
    if [ -z "$(awk -v h="$head" '$1 == "import" && $3 == "-" && $9 == h' <<< "$hold")" ]; then
      withdraws=$(relabel_withdraws "$number" "$head") \
        || { echo "::error::the comments of #$number or the import check runs of $head could not be read."; return 1; }
      read -r withdraws from <<< "$withdraws"
      case $withdraws in
        screen) because="a screen held $head" ;;
        blocking) because="a review of $head asks for a change" ;;
        person) because="a review of $head has questions for Sami" ;;
        refused) because="the fresh reader refused a review of $head" ;;
      esac
      if [ -n "$because" ]; then
        said="#$number: a hold that is not tried again names $head, and $because."
        # The reason of the line <!-- withdraw-owed <head> <why> <run> <read> -->, while no newer screened review
        # outranks it.
        if [ "${from:-}" = owed ]; then
          said="#$number: a hold that is not tried again names $head. Its label comment records a reason of an earlier"
          said+=" run to withdraw the import check runs of $head."
        fi
        echo "$said So of the App's writes of $head, the rescreen pass tries again only the withdrawal of the import" \
          "check runs. It does so only after a run whose post job failed or was cancelled."
        due_retry 'review|rescreen|relabel|approve' relabel import || return 1
      else
        echo "#$number: a hold that is not tried again names $head, and no reason to withdraw the import check runs" \
          "of $head stands. So the rescreen pass tries the App's writes of $head again as for any head, after a" \
          "review, a rescreen or a relabel whose post job failed or was cancelled."
        due_retry 'review|rescreen|relabel' relabel import || return 1
      fi
      [ -z "$taken" ] || return 0
      due_rerun
      return
    fi
    echo "#$number: a hold that is not tried again names $head: the App's writes of it are not tried again."
    due_rerun
    return
  fi
  for reason in catchup old unreviewed variable rerun; do
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
# closing run counts, whatever its outcome, but one that counts no try (tried, of facts): after REVIEW_TRIES of them it
# is not tried again (left_stopped), and nothing more of it is read (gave_up). An export pull request (exported) is due
# nothing: the pass's list of the closed pull requests gives its head repository and head branch (repository and
# branch). The trust job sets neither: its item stops an export pull request before the check of a stop calls this.
consider_closed() {
  local head="" given closing="" made="" created ended run started f post count=0 newest=""
  if exported "${repository:-0}" "${branch:--}"; then
    echo "#$number: an export pull request, from the branch $branch of this repository, of which the trust job takes" \
      "no run."
    return 0
  fi
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
    [ "${f%% *}" != try ] || count=$((count + 1))
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
