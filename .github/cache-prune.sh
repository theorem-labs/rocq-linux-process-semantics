#!/usr/bin/env bash
# Deletes the caches on this run's ref whose key starts with PREFIX and that
# are older than NEW, the cache this run just saved.
#
#   .github/cache-prune.sh PREFIX NEW
#
# A workflow calls it on a push to main, after its save. A save that failed
# logs only a warning, so the script deletes nothing when NEW is not there. Two
# pushes to main can run at once and restore the same cache, so the script
# deletes every older entry, not only the one this run restored. Then main
# keeps one cache per prefix. Needs GH_TOKEN with `actions: write`. A failure
# here never fails the job: the worst case is an old cache that GitHub evicts.
set -uo pipefail

prefix=$1
new=$2
api="repos/$GITHUB_REPOSITORY/actions/caches"
# The list can lag the save by some seconds, so the script asks up to four
# times.
created=
for attempt in 1 2 3 4; do
  if ! caches=$(gh api "$api?key=$prefix&ref=$GITHUB_REF&per_page=100" --jq '.actions_caches'); then
    echo "::warning::could not list the caches of $prefix: deleting nothing"
    exit 0
  fi
  created=$(jq -r --arg k "$new" '.[] | select(.key == $k) | .created_at' <<<"$caches")
  [ -n "$created" ] && break
  [ "$attempt" -lt 4 ] && sleep 15
done
if [ -z "$created" ]; then
  echo "::warning::the new cache $new is not on $GITHUB_REF: deleting nothing"
  exit 0
fi
jq -r --arg p "$prefix" --arg t "$created" \
  '.[] | select((.key | startswith($p)) and .created_at < $t) | "\(.id) \(.key)"' <<<"$caches" \
  | while read -r id key; do
      echo "deleting $key"
      gh api -X DELETE "$api/$id" > /dev/null || echo "::warning::could not delete $key"
    done
exit 0
