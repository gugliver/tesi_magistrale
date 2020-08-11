To test the LoadBuffer with directed tests, listed in the [Load Buffer TP](https://docs.google.com/spreadsheets/d/1cSQr6cGat1nZaBscgiUWw2k0hxVM95Rw8i-hdAh4hio/edit#gid=0), we developed a few binaries and a few modifications of the whole UVM (available on the branch `origin/feature/forced-retry`) to drive the desired `el_ids` to the LB.

**Binaries:**
1. `vl_32_split`
2. `vl_16_split`
3. `vl_8_split` 

these binaries ensure that the LoadBuffer of Lane 0 will receive element belonging to two different `element groups`, for example, in the case of `sew=32` it will receive elements with `el_id=80` and `el_id=65`.

**New sb_id modes :**
1. `RETRY` : it will force a single retry, by issuing the `cache_line` in a precise order `{0,4,8,12,16}` and then `SEQUENTIAL` as usual, sending the missing lines. Doing so will cause the following el_id sent to the LB of LANE0 : `{0,40,80,120,160}` and cause a retry (also for the others LBs).
2. `N_RETRIES` : it will send the cache line with a pace of 4 (and then sending the missing ones) causing more retries.
3. `RETRY_OOO` : it will cause a retry with out of order `el_ids` (es.: 0,40,120,80,160).

All these modes, combined with the binary `vl_64_one_retry` (masked vl with data for just the first lane), will cause only the LB of LANE 0 asking for a retry.

**New Load modes :**
1. `ALTERNATE_L`: it will send data from the two inflight load alternatively.
