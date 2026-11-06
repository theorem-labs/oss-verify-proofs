(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Export MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01N01Z37Corelib4Init9Datatypeshf3snd79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~jd4ghdrjd6region35stdpp7numbers1Nob6eq_dec46Stdlib6ZArith6BinInt1Zq52le37Corelib4Init5Logics22eqq53add25stdpp9countableu1bN_countable35stdpp7numbers1Zhg06eq_dechf3fsthf6optionhf4prodhf4Somes23and04Npos79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~hk48ticks_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~hp25rmrepjd4aptrjd4wr3225stdpp4basehub6lookup35stdpp9bitvectorbdefinitionsig12bvu1bZ_countableu1eprod_countable25stdpp9decidableik3bprod_eq_dec25stdpp4gmapim34gmapim3bgmap_lookups22or3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsiobcwrite_to_memhk42wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~it83le4it82wajd7RKGroupjd6mstatejd6r_basejd6r_kindjd5r_lenjd5rkindjdbround_up_pgjd8s_groupsjd9s_regionsq52ltq53pows23not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~joa3memhp2aRAUXV_CELL79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~ju28rauxv_okju2crpres_excepthf6lengthq56of_nathf4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kla3ivlkla5munchkla7outsidekla5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~kra5rsegs" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rmrep_wr32 : ltac2:(zQ "ic0!h9!hc!j7!nb!o2!pc!rd!t6!tb!v2!hh1!hhb!hi1!hia!hj1!hj8!hje!ho6!ht4!htd!hu4!hv7!ihe!ii4!ij2!il4!imf!in7!io6!is2!it2!jh2!jh9!jhf!ji9!jj2!jjb!jk4!jkc!jl4!jm2!jmd!jn9!jne>2st$i2>1m>0@1$h6@1$h0#k0@1$c@1$h6@1$h0#8>1p@2$d$0$1>1v$1>1r$4>0@4$h2?5HCEIL?4HSEC^5^4>0@1$h1^6>0@3$7@1$c$4@6$h5$0$4@4$ha$0$5$9$4@4$hb$0$5$9$4@3$b$0$1^5@1$i9^7@2$e$4^3>0@3$7$i6@1$i4^4$i1>0@2$6Z@3$2$0$1^7>0@2$6@2$8@3$2$0$1^8+4@1$i7@1$i5^6>0>1b@2$d$0$1>2gh$3>0@3$7@1$c$3@6$h5@2$d$0$1$3@4$ha$h3@4$h9$0$5$1$a@6$h8$0$5$9$1$a$h7$3@4$hb$h3@4$h9$0$5$1$a@6$h8$0$5$9$1$a$h7$3^2@1$i8^d@2$e$3^1>0@3$7$0@3$b$0$1^3@3$b$0$1^c@2$hc@2$6@2$8@3$2$0$1^d+4@3$2$0$1^4@2$6@2$8@3$2$0$1^4+9@3$2$0$1^d>0@2$f@2$6Z^9@2$ia^9@2$ib+2+i0@2$f@4$h2?5HCEIL?4HSEC@3$h4^b^a^d@3$hd^c@1$i0@2$8@1$i3^9@3$2$0$1^b@1$hf@1$he^a@1$h1@3$h4^b^a^d").
Proof. try hcb. try hsb.
  intros st m p v r MR TK Hr Hk H0 H4 Hg Hv.
  rewrite le4_bytes by lia.
  change (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)])
    with (write_to_mem (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)])
            (wa (r_base r + snd p) + 1) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p) + 1 + 1) [b8 ((v / 65536) mod 256)])
            (wa (r_base r + snd p) + 1 + 1 + 1) [b8 (v / 16777216)]).
  rewrite !wa_succ.
  unfold wr32.
  assert (E1 : forall q w stx, wr8 q w stx = wr8 q (w mod 256) stx) by (intros; apply wr8_mod).
  rewrite (E1 p v), (E1 (aadd p 1) (Z.shiftr v 8)), (E1 (aadd p 2) (Z.shiftr v 16)), (E1 (aadd p 3) (Z.shiftr v 24)).
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  rewrite (Z.mod_small (v / 16777216) 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (B0 : 0 <= v mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B1 : 0 <= (v / 256) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B2 : 0 <= (v / 65536) mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (B3 : 0 <= v / 16777216 < 256) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (S1 : rmrep (wr8 p (v mod 256) st) (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) /\ ticks_ok (wr8 p (v mod 256) st)).
  { split; [|apply ticks_ok_wr8; exact TK]. apply (rmrep_wr8 st m p _ r MR TK Hr Hk); [lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S1 as [M1 T1].
  assert (S2 : rmrep (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)) (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)])
               /\ ticks_ok (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st))).
  { split; [|apply ticks_ok_wr8; exact T1].
    replace (r_base r + snd p + 1) with (r_base r + snd (aadd p 1)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 1) _ r M1 T1); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S2 as [M2 T2].
  assert (S3 : rmrep (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))
                    (write_to_mem (write_to_mem (write_to_mem m (wa (r_base r + snd p)) [b8 (v mod 256)]) (wa (r_base r + snd p + 1)) [b8 ((v / 256) mod 256)]) (wa (r_base r + snd p + 1 + 1)) [b8 ((v / 65536) mod 256)])
               /\ ticks_ok (wr8 (aadd p 2) ((v / 65536) mod 256) (wr8 (aadd p 1) ((v / 256) mod 256) (wr8 p (v mod 256) st)))).
  { split; [|apply ticks_ok_wr8; exact T2].
    replace (r_base r + snd p + 1 + 1) with (r_base r + snd (aadd p 2)) by (cbn; lia).
    apply (rmrep_wr8 _ _ (aadd p 2) _ r M2 T2); cbn; [exact Hr| exact Hk| lia| |lia].
    intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia. }
  destruct S3 as [M3 T3].
  split; [|apply ticks_ok_wr8; exact T3].
  replace (r_base r + snd p + 1 + 1 + 1) with (r_base r + snd (aadd p 3)) by (cbn; lia).
  apply (rmrep_wr8 _ _ (aadd p 3) _ r M3 T3); cbn; [exact Hr| exact Hk| lia| |lia].
  intros b gh Hb Hfb. destruct (Hg b gh Hb Hfb); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rauxv_ok_pres : ltac2:(zQ "a0!hc!jo4!jsd!jt4!ki5!rd!hj8!kj1!tb!jn9>1C>0$0P>1m$2>2m'$2>1B$0>0@4$4?5HCEIL?4HSEC^3^1>0@3$7^5^4^3>0>1a$0>0@2$5^4^1@1$1@1^8^2>0>1a$0>0@2$6@2$5$3^1@2$9^1@2$8$3+8@1$1@1^9^2@4$4?5HCEIL?4HSEC^6^5").
Proof. try hcb. try hsb.
  (intros C m m' B nd_i1 HP HB HC; ndestruct nd_i1 as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H)).
  nexists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_write : ltac2:(zQ "f0!hje!hc!rd!ihe!kk1!jsd!kj1!tb!kka!kl3!hj8!is2!jh9!jn9!jne>1C>0$1P>2m0$5>1m$5>1a$1>2bs@1$9@1$3@1$0#8>0@3$6^5^4^3>0@2$2Z^3>0@2$2@2$7^4@1$8@2$4@1$3@1$0#8^3@2$e+2+k0>0>1x$1>0@2$a@2$2^6^1@2$d^1@2$7^6@1$8@2$4@1$3@1$0#8^5@1^a^2@3$6^9^8@3$b^7@1$c^6^5").
Proof. try hcb. try hsb.
  intros C m0 m a bs HP Ha Hl HC x Hx HCx.
  destruct (HP x Hx HCx) as [E W].
  assert (NE : write_to_mem m (wa a) bs (wa x) = m (wa x)).
  { rewrite write_to_mem_spec by lia. rewrite wa_unsigned by lia.
    destruct (Z.leb_spec0 a x); destruct (Z.ltb_spec0 x (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    exfalso. apply HCx, HC. lia. }
  split.
  - rewrite NE. exact E.
  - intros Hw. apply wview_write_mono. apply W, Hw.
Qed.

Lemma rpres_except_munch_frame : ltac2:(zQ "h10!hje!hc!jsd!kj1!ihe!kl3!hi1!hj8!jo4!kp6!kpd!kq6!kr1!kv7!rd!jn9!jne>1C>0$1P>2m0$2>1m$2>2m'>0@1$4@1$0#k0@1$6@1$4@1$0#8>1W@1$5$9>0@3$3^5^4^3>0@3$a^2^4^3>0@3$c$d^5^4>0>1x$1>0@2$7@2$eZ^1@2$f^1@2$h0+2+k0>0@1$8@1^a^2@2$b^7^3@3$3^9^8^6").
Proof. try hcb. try hsb.
  intros C m0 m m' W HP MU WM HW. eapply rpres_except_trans; [exact HP|]. eapply rpres_except_of_munch; eauto.
Qed.

End HCW.

(* [comment removed for export] *)
