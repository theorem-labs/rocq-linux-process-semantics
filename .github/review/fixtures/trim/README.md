# Fixtures of the trim test

These files come from the trim test of dispatch://OSSV-221/artifact/trim-test-md.
`lists/` and `out-l/` are byte-for-byte copies of the same folders in
`gs://theorem-ossv-runs/handover/OSSV-221/trim/`. Each file of `lists/` holds
the items of one review comment. The file of `out-l/` with the same number
holds the comment that a Claude session trimmed with that list.
`.github/test_review.py` checks that `.github/review/trim.py` adds no item to
any of the 30 trimmed comments.
