# shellcheck shell=bash
# trusted.sh: the one rule of which accounts have write access, as the review workflow reads it. Three steps source this
# file, each before the first call of trusted:
# - the gather job's step "Gather the pull request or issue" of .github/workflows/review.yml, which reads the comments
#   of the author and of each account that trusted passes;
# - the trust job's step "Whether the author and the account that started the run have write access" of review.yml;
# - the step "Start the runs that the open items are due" of .github/workflows/rescreen.yml, the rescreen pass.
# The last two steps source held.sh, the file beside this one, after this file, and the functions of held.sh call
# trusted too.
# The gather job checks out main. The other two jobs check out this file and held.sh alone, at the commit whose workflow
# file runs (github.sha, a commit of main). So a file of main runs, and never a file of a pull request.
# trusted reads APPS and REPO from the environment of the step. The source line defines permission_of and trusted, and
# reads nothing from GitHub.

# trusted <login>: 0 when <login> is one of the APPS, or an account that GitHub's collaborator permission API gives
# admin or write; 1 when it is neither; 2 when the API could not say. The API is asked once for each login in the step
# that sources this file (permission_of).
declare -A permission_of=()
trusted() {
  local permission
  [[ $1 =~ ^[A-Za-z0-9-]+(\[bot\])?$ ]] || return 1
  [[ ,$APPS, != *",$1,"* ]] || return 0
  [[ $1 != *'[bot]' ]] || return 1
  if [ -z "${permission_of[$1]+set}" ]; then
    permission=$(gh api "repos/$REPO/collaborators/$1/permission" --jq .permission) || return 2
    permission_of[$1]=$permission
  fi
  [[ ${permission_of[$1]} == admin || ${permission_of[$1]} == write ]]
}
