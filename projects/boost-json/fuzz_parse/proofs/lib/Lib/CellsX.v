(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hc5wr_at04Npos46Stdlib6ZArith6BinInt1Zm43addm42le35stdpp9bitvectorbdefinitionso72bv37Corelib4Init9Datatypesq94listq96option37Corelib4Init5Logict13andt13iff3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypev17Segment79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hj04cell79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hn48rw_cellsq93apphj0acells_sizem46of_natq94consq93nilhj02CBq93nat37Corelib4Init3Nathv13sub37Corelib4Init5Peanoiga2le37Corelib5Lists7ListDefii46firstnii45skipnhv13add" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Lemma wr_at_app : ltac2:(zQ "b0!h9!l6!le!nc!o2!q4!s1!s8!u5!ub!hi6>4segs@1$6$a>1m>0@1$5@1$2#k0@1$7@1$5@1$2#8>1a$0>2n1$0>2n2$0>0@2$4Z^2>0@2$4Z^2@2$9@4$1^7^6^5@2$3^4^3@2$8@4$1^7^6^5^4@4$1^7^6@2$3^5^4^3").
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.

Lemma rw_cells_app : ltac2:(zQ "e0!s1!hmc!hqf!le!q4!hrb!s8!u5!ub!h9!hi6!hs1!nc!hsf>4segs@1$0$a>1m>0@1$4@1$3#k0@1$6@1$4@1$3#8>1A$9>3cs1@1$0$1>3cs2@1$0$1@2$8@4$2^5^4^3@3$5$1^2^1@2$7@4$2^5^4^3^2@4$2^5^4@2$c^3@1$d@1$b^2^1").
Proof.
  intros segs m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite wr_at_app by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_split : ltac2:(zQ "h30!hmc!le!q4!ht8!htf!hu5!hqf!s1!hub!s8!u5!ig3!ihe!ijb!ik5!h9!hi6!nc!hsf>4segs@1$7$h0>1m>0@1$2@1$1#k0@1$9@1$2@1$1#8>1A$f>1n$8>1k$8>4junk@1$7@1$2@1$1#8>0@4$6^6^5^4@3$3$0@2$5^3^1@1$4$0>0@2$c^3^4@2$a@4$6^8^7^6@3$3$0@2$5^4@3$d@1$2@1$1#8^4^3@1$4$0@4$6^8^7@2$h1^6@1$h2^4@3$3$0@2$5@2$b^5^4@3$e@1$2@1$1#8^4^3@1$4$0").
Proof.
  intros segs m A n k junk H Hk.
  assert (E : rw_cells segs m A ([CB k (firstn k junk)] ++ [CB (n - k) (skipn k junk)])).
  { destruct H as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [L _].
    split; [split|].
    - cbn. rewrite firstn_length, skipn_length. repeat split; lia.
    - cbn [cells_bytes cbytes app]. rewrite app_nil_r, firstn_skipn. cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. exact Hb.
    - cbn [cells_size csize app] in *. replace (k + (n - k + 0))%nat with (n + 0)%nat by lia. exact Hw. }
  apply rw_cells_app in E. cbn [cells_size csize Nat.add] in E. rewrite Nat.add_0_r in E. exact E.
Qed.

Lemma rw_cells_CB_join : ltac2:(zQ "h00!hmc!le!q4!ht8!s1!htf!hu5!hqf!hub!hrb!s8!ike!h9!hi6!nc!hsf>4segs@1$4$d>1m>0@1$2@1$1#k0@1$a@1$2@1$1#8>1A$c>2n1$8>2n2$8>2b1@1$4@1$2@1$1#8>2b2@1$4@1$2@1$1#8>0@4$7^7^6^5@3$3$0@2$6^4^2@1$5$0>0@4$7^8^7@2$e^6@1$f^5@3$3$0@2$6^4^2@1$5$0@4$7^9^8^7@3$3$0@2$6@2$b^6^5@3$9@1$2@1$1#8^4^3@1$5$0").
Proof.
  intros segs m A n1 n2 b1 b2 H1 H2.
  assert (E : rw_cells segs m A ([CB n1 b1] ++ [CB n2 b2])).
  { apply rw_cells_app. cbn [cells_size csize]. rewrite Nat.add_0_r. split; assumption. }
  destruct E as [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as (L1 & L2 & _).
  split; [split|].
  - cbn. rewrite length_app. repeat split; lia.
  - cbn [cells_bytes cbytes app] in *. rewrite app_nil_r in *. exact Hb.
  - cbn [cells_size csize app] in *. rewrite Nat.add_0_r in *. replace (n1 + n2 + 0)%nat with (n1 + n2)%nat by lia. exact Hw.
Qed.
