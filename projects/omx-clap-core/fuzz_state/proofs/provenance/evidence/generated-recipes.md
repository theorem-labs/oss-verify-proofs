# Generated files: index of their hand-written recipe lines (class X16)

The verbatim text of each line is in the unit's internal record (ref and path in the series' PR body), checked by the
sha256 below. Here: the file, the line, the number of lines, the sha256 of the line's text, and what the series does.

| file | line | lines | sha256 of the text | series |
|---|---|---|---|---|
| lib/A/AD25.v | 5 | 1 | afb0d4d0b6cb3dcf621cf65708fcefc654f786faadccae19dd5521912e77d9ff | removed: regenerated |
| lib/A/AD1o.v | 5 | 1 | 74780e211dc7e01c9297665487b7813c67b1f1d1f84af73f843c1397da146ddd | removed: regenerated |
| lib/B/YB12.v | 5 | 1 | 5aa2cb8449977a1badd34d210bb167ad82028123ce663c35efc4b9c3e2d0c2e8 | removed: regenerated |
| lib/B/YB1m.v | 5 | 1 | f7a50e93a663a538bcbaf398d6101dd0fa3a952ddbe71284a8b9a474c01c94c7 | kept here; lane-comments removes it |

## How the three regenerated files are reproduced

- lib/A/AD25.v and lib/A/AD1o.v: gen_zsh_consumers.py, sha256 fab3448077a211afc8b288dd5af7c2d43fb15972c8f17266b73264519e7729aa. Inputs, under lib/A/:
  AF0m.v at 9a979984f23e (sha256 14b9ee8d84ffbd8fc62ba35cba1dea517b6b6be245914a720f31294d21d46929), AD20.v at 9a979984f23e (4ff8ae4405ee6a9cb6becbdfea5fdfb58cb5b0ec21eb1602cded7e01685c757b),
  AE3m.v at 9a979984f23e (12d6d992138c57f67861abafa31e8757261598d63c2d7d08af9416af5bd46d41), and AD25.v / AD1o.v at b04db294041 (21cb720acc05dca6ee784e1fb8ced361025c7de467683e2907ac08295cc5f5d4 /
  54ad84d19f5b2130595c9d9ad32e35dfc4a77d3bd081a275c471281b07c88c7b). Command `gen_zsh_consumers.py --af0m AF0m.v --ad20 AD20.v --ae3m AE3m.v --ad25 AD25.v
  --ad1o AD1o.v --out-dir OUT`, rc 0. The output equals the 9a979984f23e files except line 5.
- lib/B/YB12.v: atable.py, sha256 7b569be5151fa55d9a3614ea8418e11bd8d3e6b5b896888467ae74bb866611ec, on the pinned fuzz_state.asan-ubsan (sha256
  5ac5ce0954f87e2d050c481b7b0599cfd55ef554eadc008e51491f44c053d204) and its unstripped twin (sha256
  b1566a1ca816049d20588a70b9b43f152a338319c8ebea649df5b62ff5c4cc00). Command `atable.py PIN TWIN --side B --prefix
  OssFuzzTheorems.Proofs.omx_clap_core.fuzz_state.lib --reusable .Reusable`, rc 0. Its 17 lines equal lines 6-22 of the
  9a979984f23e file; lines 1-4 are the licence lines.
- lib/B/YB1m.v line 5 records a check, not a generator: the start-up collector certificate's result on this unit's
  YB05, YB12 and the 50 states of YB01, rc 0, whose shape equals cgif_file_fuzzer's. Its full text is in the internal record.
