(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1f.v, with its module paths changed; its address literals moved to omx-clap-core/fuzz_preset's ASan build where h-mani-a2's maps/reloc-cgif-preset.A.tsv maps them; the literals it does not map are still cgif_file_fuzzer.asan's (listed in the commit that moved them). *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 ('the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob ede269051fa1); a re-relocation of this file from cgif must be checked against that edit. *)
(* Modified by Theorem Labs, 2026-10: for the world field w_H8 (YA0n), W0 and tfib_AR_init pass W1 the proof H1_H8 of the image-A twin lib/A/PWorldH8.v; tfib_AR_init names its Hve / Hfit / Hch / HC premises to state it (fm's form, lib/A/AD1f.v:17, :95-96, :257-272). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD1f.v, with its module paths and module names changed; 82 of its 141 lines of code are new or changed and 217 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the revision's launch (CONFIG_RSEQ-sized auxv, execfn, group id, launch premises); the input-owned, top-anchored launch stack; the start-up certificate per CONFIG_RSEQ flag with states computed in the build). *)
(* Image B (fuzz_reply.asan-ubsan) twin of lib/A/AStkCov.v, the same text with the B module names (YD1g, YD2i,
   YB1v, YF0m, YB01r, YB12, YB1h, YB13, B/StartStkAuxG, B/StartStkAux; images AsanUbsan; YStkUp for AStkUp) and B's
   hull top 0x5fc000 (B/YB12.v img_hi).  The covered-range fact of StartupTrace's step (2) for the asan-ubsan image: at main's hand-off, FULL is defined on every
   byte of the entry image from the entry sp up to the entry page top, [usp, entry_page_top rdraw) (entry_stk_cov), the
   conclusion of A/AD1pcf.v's handoff_cov and B/YStkUp.v's Section hypothesis HCOV; tfib_handoff_stk_up_cov is
   YStkUp's tfib_handoff_stk_up with HCOV discharged.
   LPS 727298f3: the entry image runs from the entry sp to the stack VMA's end ed_top (Run.v entry_page_top), and it
   tiles as plugin-hostd/fuzz_command's B/YD1p.v reads its stack top (C = block_head_size at the run's own CONFIG_RSEQ
   flag, G = STACK_ROUND's gap in words, W = the arch_align_stack pad):
     [usp, usp + 24)              argc, argv[0], argv[1] or argv's NULL   kn rows at eSp0, 24 bytes (kn_vis_args)
     [usp + 24, utop) where argH0 holds (Reusable/YA02.v: the argv tail and the envp array, STACK_ROUND's gap 8 G,
                                  the pad W, the strings)   the start-up memory (HM), defined up to ed_top
     [usp + 24, utop) where argH0 does not hold, by YA02.argH0_false_cases one of
       [A, A + AUXSZ)             the auxv's 27 or 29 pairs               the hand-off's KUnk row (B/StartStkAuxG.v)
       [usp + C - 16, usp + C)    the AT_RANDOM bytes                     the hand-off's KBlob row (B/StartStkAuxG.v)
   A kn row byte is above the image hull, so seg_rom is None there and the reader's byte is FULL's (kn_cov and
   StartStkAuxG.vis_present, through YA0j.ho_vis_range); an argH0 byte is the start-up memory (HM), which is defined
   from usp up to ed_top (wrap_mem_entry_defined, from YK11.length_entry_stack_image_launch, as curl/fuzz_bufq's
   lib/R/A/AStkCov.v). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import AsanUbsan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP09 YK00 YK04 YA0i YA0n YK0g YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB12 YB1h YB13 YB01r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0r.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YD1h.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YD1g YD2i StartStkAuxG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YK0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YStkUp StartStkAux.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
(* the argc word and argv[0..1] (or argv's NULL) at e_sp0 + 0, 8, 16 (YK09.init_kn_with's three KWord rows), on every
   hand-off state of both CONFIG_RSEQ flags *)
Lemma kn_vis_args : forallb (fun c => kn_vis TFIB c eSp0 0 24) HS_tfib_list_all = true.
Proof. vm_compute. reflexivity. Qed.
Section c. Context {fx : YK11.FPState}.
(* the start-up memory is defined from the entry sp up to ed_top (the entry image is the whole block,
   YK11.length_entry_stack_image_launch), from YK11.wrap_above_sp and YK0n.stm_at (curl/fuzz_bufq's
   lib/R/A/AStkCov.v) *)
Lemma wrap_mem_entry_defined : forall inp mbase ph entry (sp brk : word) draw (x : word),
entry_launch_ok_va Sv48 (mkEntry sp brk mbase draw) inp ->
bv_unsigned sp <= bv_unsigned x -> bv_unsigned x < bv_unsigned (ed_top draw) ->
YK11.wrap_mem inp mbase ph entry sp draw x <> None.
Proof.
intros inp mbase ph entry sp brk draw x Hok Hlo Hhi.
pose proof (YK11.length_entry_stack_image_launch Sv48 inp mbase ph entry sp brk draw Hok) as HT.
assert (Hi : (Z.to_nat (bv_unsigned x - bv_unsigned sp) < length (entry_stack_image inp mbase ph entry sp draw))%nat) by lia.
assert (Hai : bv_unsigned x = bv_unsigned sp + Z.of_nat (Z.to_nat (bv_unsigned x - bv_unsigned sp))) by lia.
rewrite (YK11.wrap_above_sp inp mbase ph entry sp draw x Hlo).
rewrite (YK0n.stm_at sp _ x _ Hi Hai).
apply nth_error_Some. exact Hi.
Qed.
Section d.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Variables (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
Hypothesis Hinp : valid_input inp.
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
Variable SINV : env -> (word -> option byte) -> Prop.
#[local] Notation argH := (YA02.argH0 sp rdraw argv envp
  (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation entryw := (Z_to_bv 64 (Z.of_N AsanUbsan.M.init_pc)).
Hypothesis SINV_sp0 : forall E' M, SINV E' M -> uE E' e_sp0 = TOP + 8388608.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk argv envp
  (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp) (in_hwcap inp) (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem inp mbase TPH entryw sp rdraw a.
Context {rc : YM05.RunCeil}.
Hypothesis Hceil : YM05.ceil_of_top (bv_unsigned sp - stack_max_size).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation ly0 := (YD1g.ly0 ch E model).
#[local] Notation H1 := (YD2i.H1 sp rdraw inp ch E model).
#[local] Notation u := (uE E).
#[local] Notation krs := (kb_rseq (in_kernel inp)).
Ltac inst H := try specialize (H fx); try specialize (H B); try specialize (H HB); try specialize (H sp); try specialize (H rdraw);
try specialize (H brk); try specialize (H mbase); try specialize (H inp);
try specialize (H Hsp); try specialize (H Hva); try specialize (H Hve); try specialize (H Hfit);
try specialize (H Hvl); try specialize (H Hlau); try specialize (H Hinp);
try specialize (H h); try specialize (H ch); try specialize (H E); try specialize (H R); try specialize (H FULL);
try specialize (H model); try specialize (H Hch); try specialize (H SINV); try specialize (H SINV_sp0);
try specialize (H HC); try specialize (H HE); try specialize (H HM); try specialize (H rc); try specialize (H Hceil).
Ltac get L := let H := fresh "L" in pose proof L as H; inst H; exact H.
#[local] Definition uS0 := ltac:(get YD2i.uS0).
#[local] Definition u_auxb := ltac:(get YD2i.u_auxb).
#[local] Definition u_atrb := ltac:(get YD2i.u_atrb).
Let Hvis := ho_vis_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) tfib_in_hull tfib_hull_ok E ch R FULL model HC.
(* a byte a kn row covers: the reader's byte is defined (Hvis), and above the image hull it is FULL's *)
Lemma kn_cov : forall rb rk len, forallb (fun c => kn_vis TFIB c rb rk len) HS_tfib_list_all = true ->
forall a, u rb + rk <= a < u rb + rk + len -> 0x5fc000 <= a < 2 ^ 64 -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros rb rk len K a Ha Hz.
pose proof (proj1 (forallb_forall _ _) K ch (HS_tfib_r_In _ h ch Hch)) as Kc. cbn beta in Kc.
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
(* a byte argH0 covers: FULL is the start-up memory there (HM), defined from usp up to ed_top *)
Lemma argH_cov : forall a, argH E (Z_to_bv 64 a) = true -> usp <= a < bv_unsigned (ed_top rdraw) -> 0 <= a < 2 ^ 64 ->
FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Hg Ha Hz. rewrite (HM _ Hg).
apply (wrap_mem_entry_defined inp mbase TPH _ sp brk rdraw (Z_to_bv 64 a) Hlau); rewrite u64_lit by exact Hz; lia.
Qed.
(* HCOV of B/YStkUp.v, verbatim *)
Lemma entry_stk_cov : forall a, usp <= a < entry_page_top rdraw -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha. unfold entry_page_top in Ha.
pose proof Hsp as (SL & SH & _). unfold sp_window_lo in SL. unfold sp_window_hi in SH.
pose proof (YK11.length_entry_stack_image_launch Sv48 inp mbase TPH entryw sp brk rdraw Hlau) as HLEN.
pose proof uS0 as U0. pose proof u_auxb as UA. rewrite snd_auxb in UA. pose proof u_atrb as UR.
pose proof (StartStkAux.stk_aux_chk_of krs h ch Hch) as Hchk.
assert (Ha64 : 0 <= a < 2 ^ 64) by (pose proof (bv_unsigned_in_range 64 (ed_top rdraw)) as T;
  change (bv_modulus 64) with (2 ^ 64) in T; lia).
assert (Hlo : 0x5fc000 <= a) by (clear - Ha SL; lia).
destruct (Z_lt_le_dec a (usp + 24)) as [C1|C1].
{ apply (kn_cov eSp0 0 24 kn_vis_args); [rewrite U0; clear - Ha C1; lia | clear - Hlo Ha64; lia]. }
destruct (argH E (Z_to_bv 64 a)) eqn:Hg.
{ exact (argH_cov a Hg Ha Ha64). }
assert (HFC : (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24 <= bv_unsigned (Z_to_bv 64 a)
< usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 456 + 32 * rseq_z krs)
\/ (usp + Z.of_nat (block_head_size krs argv envp) - 16 <= bv_unsigned (Z_to_bv 64 a)
< usp + Z.of_nat (block_head_size krs argv envp))).
{ (* [YA02.argH0_false_cases]'s own proof at this input: its exported binder list leads with section
     variables this file does not hold ("sp" given where a segment list is expected). *)
  unfold YA02.argH0, YA02.argH0_core in Hg. cbv zeta in Hg.
  cbn [in_kernel YA02.inp recorded_kernel kb_rseq] in Hg.
  rewrite u64_lit in Hg |- * by exact Ha64.
  repeat rewrite orb_false_iff in Hg.
  destruct Hg as ((((H1 & H2) & Ht) & Hg5) & Hp).
  apply andb_false_iff in H1, H2, Ht, Hg5, Hp.
  destruct H1 as [H1|H1], H2 as [H2|H2], Ht as [Ht|Ht], Hg5 as [Hg5|Hg5], Hp as [Hp|Hp];
    rewrite ?Z.leb_gt, ?Z.ltb_ge in H1; rewrite ?Z.leb_gt, ?Z.ltb_ge in H2; rewrite ?Z.leb_gt, ?Z.ltb_ge in Ht;
    rewrite ?Z.leb_gt, ?Z.ltb_ge in Hg5; rewrite ?Z.leb_gt, ?Z.ltb_ge in Hp; lia. }
rewrite u64_lit in HFC by exact Ha64.
destruct HFC as [HFC|HFC].
- apply (stk_auxv_present TOP SINV _ (in_fs inp) E ch R FULL model (rseq_z krs) HC Hchk);
  [unfold AUXSZ; lia | lia].
- apply (stk_atr_present TOP SINV _ (in_fs inp) E ch R FULL model (rseq_z krs) HC Hchk); lia.
Qed.
(* YStkUp.tfib_handoff_stk_up with its HCOV discharged by entry_stk_cov *)
Theorem tfib_handoff_stk_up_cov : forall a, usp <= a < ly_top ly0 -> aview tfibsegs H1 FULL a <> None.
Proof. pose proof YStkUp.tfib_handoff_stk_up as T. inst T. exact (T entry_stk_cov). Qed.
End d.
End c.
