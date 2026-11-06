(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1f.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 (cold/h-hpreset-7-r1-memnorm bad7e00334f, 'the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob ede269051fa1); a re-relocation of this file from cgif must be checked against that edit. *)
(* Modified by Theorem Labs, 2026-10: for the world field w_H8 (YA0n), W0 and tfib_AR_init pass W1 the proof H1_H8 of the image-A twin lib/A/PWorldH8.v; tfib_AR_init names its Hve / Hfit / Hch / HC premises to state it (fm's form, origin/cold/port-fm-rtprintf-param 3e35620c52e lib/A/AD1f.v:17, :95-96, :257-272). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD1f.v, with its module paths and module names changed; 70 of its 129 lines of code are new or changed and 217 lines of the source are left out. *)
(* The covered-range fact of StartupTrace's step (2) for the asan image: at main's hand-off, FULL is defined on every
   byte of the entry image from the entry sp up to the entry page top, [usp, entry_page_top sp bsb).  This is AStkUp.v's
   Section hypothesis HCOV, proved here over AStkUp's Section, and tfib_handoff_stk_up_cov is AStkUp's
   tfib_handoff_stk_up with HCOV discharged.

   The range tiles into six pieces with no gap.  Three are rows of each hand-off state's own knowledge (kn), decided on
   the 50 closed states by vm_compute and read through ho_vis_range (YA0j.v), as AD1g.v's xvis_sound reads its rows;
   a row byte is above the image hull, so seg_rom is None there and the reader's byte is FULL's:
     [usp, usp + 24)               the argc word and argv[0..1]   base eSp0 (= e_sp0) + 0, 24 bytes   kn_vis_args
     [z_auxv, z_strs)              the 20 auxv words              base B5 + 24, 160 bytes             kn_vis_auxv
     [z_rand, usp + |bsb|)         the 16 AT_RANDOM bytes         base BR + 184, 16 bytes             kn_vis_rand
   The other three are argH0's clauses (YA02.v), where the hand-off memory is the start-up memory (HM) and the start-up
   memory is defined from usp up to the page top (AEntryRead.wrap_mem_entry_range):
     [usp + 24, z_auxv)            argv[2..], argv's NULL, envp and its NULL     argH0's first clause
     [z_strs, z_rand)              the argument and environment strings, pad     argH0's second clause (AD2i.argH_range2)
     [usp + |bsb|, entry_page_top) the slack above the random bytes              argH0's third clause *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB12 AB1h AB13 AB01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AD1g AD2i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require ReplyWorldH8.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AEntryRead AStkUp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
(* the three kn rows, on every hand-off state *)
Lemma kn_vis_args : forallb (fun c => kn_vis TFIB c eSp0 0 24) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma kn_vis_auxv : forallb (fun c => kn_vis TFIB c B5 24 160) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma kn_vis_rand : forallb (fun c => kn_vis TFIB c BR 184 16) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Section c. Context {fx : YK11.FPState}.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation bsb := (build_stack_bytes TPH sp argv envp uid hw rdraw).
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 TPH sp rdraw brk argv envp uid hw) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem TPH sp argv envp uid hw rdraw a.
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation ly0 := (AD1g.ly0 ch E model).
#[local] Notation H1 := (AD2i.H1 sp rdraw inp ch E model).
#[local] Notation u := (uE E).
Ltac inst H := try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw); try specialize (H brk); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit); try specialize (H h); try specialize (H ch);
try specialize (H E); try specialize (H R); try specialize (H FULL); try specialize (H model); try specialize (H Hch); try specialize (H HC);
try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
(* W1 carries the world field w_H8 (Reusable/YA0n.v); its proof at this hand-off state is lib/A/ReplyWorldH8.v's H1_H8. *)
#[local] Definition H1H8 := ltac:(get @ReplyWorldH8.H1_H8).
#[local] Notation W1 := (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1H8).
#[local] Definition uS0 := ltac:(get AD2i.uS0).
#[local] Definition uB5 := ltac:(get AD2i.uB5).
#[local] Definition uBR := ltac:(get AD2i.uBR).
#[local] Definition argH_range2 := ltac:(get AD2i.argH_range2).
Let Hvis := ho_vis_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) tfib_in_hull tfib_hull_ok E ch R FULL model HC.
(* a byte a kn row covers: the reader's byte is defined (Hvis), and above the image hull it is FULL's *)
Lemma kn_cov : forall rb rk len, forallb (fun c => kn_vis TFIB c rb rk len) HS_tfib_list = true ->
forall a, u rb + rk <= a < u rb + rk + len -> 0x5fb000 <= a < 2 ^ 64 -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros rb rk len K a Ha Hz.
pose proof (proj1 (forallb_forall _ _) K ch (HS_tfib_In h ch Hch)) as Kc. cbn beta in Kc.
pose proof (Hvis _ _ _ Kc (a - (u rb + rk)) ltac:(clear - Ha; lia)) as X.
replace (u rb + rk + (a - (u rb + rk))) with a in X by (clear; lia).
destruct (FULL (Z_to_bv 64 a)) as [b|] eqn:HF; [discriminate|]. exfalso.
assert (HS : seg_rom TSEGS (Z_to_bv 64 a) = None).
{ apply seg_rom_none_of_find. apply tfib_in_hull. unfold APSG.in_hull. cbn [img_lo img_hi TFIB]. rewrite u64_lit by (clear - Hz; lia).
  apply andb_false_iff. right. apply Z.ltb_ge. clear - Hz. lia. }
assert (HR : mrestrict (hid TFIB TOP argH E ch model) FULL (Z_to_bv 64 a) = None).
{ unfold mrestrict. destruct (hid TFIB TOP argH E ch model (Z_to_bv 64 a)); [reflexivity | exact HF]. }
unfold hreader, mbyte, Mr in X. rewrite HR, HS in X. exact (X eq_refl).
Qed.
(* a byte argH0 covers: FULL is the start-up memory there (HM), defined from usp up to the page top *)
Lemma argH_cov : forall a, argH E (Z_to_bv 64 a) = true -> usp <= a < entry_page_top sp bsb -> 0 <= a < 2 ^ 64 ->
FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Hg Ha Hz. rewrite (HM _ Hg).
exact (AEntryRead.wrap_mem_entry_range TPH sp argv envp uid hw rdraw usp (entry_page_top sp bsb) (Z.le_refl _) (Z.le_refl _) a Ha Hz).
Qed.
Lemma page_top_bound : usp + Z.of_nat (length bsb) <= entry_page_top sp bsb < 2 ^ 63 + 4096.
Proof.
pose proof (YP08.length_bsb TPH sp argv envp uid hw rdraw) as LB.
pose proof (YP08.layout_facts sp argv envp Hsp Hva Hve) as (_ & _ & _ & _ & _ & L6 & _). unfold YP08.z_rand in L6.
unfold entry_page_top, page_round_up_Z, entry_block_top, page_size.
set (n := Z.of_nat (length bsb)) in *. set (r := Z.of_nat (YP08.rand_off argv envp)) in *.
pose proof (Z.div_mod (usp + n + 4096 - 1) 4096 ltac:(lia)) as Dm. pose proof (Z.mod_pos_bound (usp + n + 4096 - 1) 4096 ltac:(lia)) as Bm.
clear - LB L6 Dm Bm. lia.
Qed.
(* HCOV of AStkUp.v:66, verbatim *)
Lemma entry_stk_cov : forall a, usp <= a < entry_page_top sp bsb -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha.
pose proof page_top_bound as PT.
pose proof Hsp as (SL & SH & _). unfold sp_window_lo in SL. unfold sp_window_hi in SH.
pose proof (YP08.length_bsb TPH sp argv envp uid hw rdraw) as LB.
pose proof (YP08.layout_facts sp argv envp Hsp Hva Hve) as (L1 & L2 & L3 & _).
assert (ZR : YP08.z_rand usp argv envp = usp + Z.of_nat (YP08.rand_off argv envp)) by reflexivity.
pose proof uS0 as U0. pose proof uB5 as U5. pose proof uBR as UR.
assert (Ha64 : 0 <= a < 2 ^ 64) by (clear - Ha PT SL; lia).
assert (Hlo : 0x5fb000 <= a) by (clear - Ha SL; lia).
destruct (Z_lt_le_dec a (usp + 24)) as [C1|C1].
{ apply (kn_cov eSp0 0 24 kn_vis_args); [rewrite U0; clear - Ha C1; lia | clear - Hlo Ha64; lia]. }
destruct (Z_lt_le_dec a (YP08.z_auxv usp argv envp)) as [C2|C2].
{ apply argH_cov; [|exact Ha|exact Ha64].
  unfold YA02.argH0. cbn beta zeta. rewrite u64_lit by exact Ha64.
  apply orb_true_iff. left. apply andb_true_iff.
  split; [apply Z.leb_le | apply Z.ltb_lt]; clear - C1 C2 L1 L2; lia. }
destruct (Z_lt_le_dec a (YP08.z_strs usp argv envp)) as [C3|C3].
{ apply (kn_cov B5 24 160 kn_vis_auxv); [rewrite U5; clear - C2 C3 L1 L2 L3; lia | clear - Hlo Ha64; lia]. }
destruct (Z_lt_le_dec a (YP08.z_rand usp argv envp)) as [C4|C4].
{ apply argH_cov; [|exact Ha|exact Ha64]. apply argH_range2. clear - C3 C4; lia. }
destruct (Z_lt_le_dec a (usp + Z.of_nat (length bsb))) as [C5|C5].
{ apply (kn_cov BR 184 16 kn_vis_rand); [rewrite UR; clear - C4 C5 LB ZR; lia | clear - Hlo Ha64; lia]. }
apply argH_cov; [|exact Ha|exact Ha64].
unfold YA02.argH0. cbn beta zeta. rewrite u64_lit by exact Ha64.
apply orb_true_iff. right. apply orb_true_iff. right. apply andb_true_iff.
split; [apply Z.leb_le | apply Z.ltb_lt]; clear - C5 Ha; lia.
Qed.
(* AStkUp.tfib_handoff_stk_up with its HCOV discharged by entry_stk_cov *)
Theorem tfib_handoff_stk_up_cov : forall a, usp <= a < ly_top ly0 -> aview tfibsegs (w_H W1) FULL a <> None.
Proof. pose proof AStkUp.tfib_handoff_stk_up as T. inst T. exact (T entry_stk_cov). Qed.
End d.
End c.
