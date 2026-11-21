(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/StackUpMainA.v, with its module paths and numbers changed; 14 of its 242 lines of code are new or changed and 12 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the hand-off states computed per CONFIG_RSEQ flag, the abstract start-up invariant, argH0 over the input's fields, the launch premise, and the entry stack laid out from the stack VMA's end: above the entry sp + 24 every byte is argH0's, an auxv word's or an AT_RANDOM byte's, read as plugin-hostd/fuzz_command's A/AD1p.v and A/StartStkAuxG.v read them). *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, lane StartupCert; rule 24: no function proved, start-up certificate layer). Image A'.
   The main-entry presence of the live stack [usp - 64 KiB, ly_top), from the start-up certificate cs_ok at main's
   entry. The layout's top bound is the driver's top_ok (lib/A/AD1v.v, usp - 160 <= ly_top <= usp + 3920), not a
   repeated constant, so stack_up_main_W1_A is the driver walk's premise lib/A/PresetD1pA.v H_stackup_main_A (lane
   StackDrv).
   - R1 half: H1 (lib/A/AD2i.v H1) hides no byte at or above TOP = usp - 8 MiB: an argH0 byte is not hidden, and any
     other byte there is visible (Reusable/YA0j.v ho_hid_high).
   - Presence half (LPS 727298f3): FULL, the memory at main's entry, has a byte at every address of
     [usp - 64 KiB, ly_top):
     [usp - WDEPTH, usp) by the stack KWr of every hand-off state (store_ok over Mr);
     [usp, usp + 24) by the KWords at usp + 0 / 8 / 16;
     [usp + 24, ly_top): ly_top is at or below the stack VMA's end (both page boundaries, the end above the entry
     sp: the launch premise entry_launch_ok_va), and the image runs from sp to that end; an argH0 byte has its
     image value (HM), and a byte argH0 leaves out is an auxv word or an AT_RANDOM byte (YA02.argH0_false_cases),
     which every hand-off state's knowledge covers (stk_aux_chk, the start state's KUnk over the vector and KBlob
     over the random bytes, kept to the hand-off).
   The hand-off facts are checked over each flag's computed hand-off states by vm_compute (stk_chk_all,
   stk_aux_all). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.omx_clap_core.fuzz_preset.images Require Import Asan.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YP08 YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB12 AB1h AB01r AD2i.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AD1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.

Definition kw_at (ch : acs) (b : expr) (k : Z) : bool :=
  existsb (fun K => match K with
                    | KWord a w _ => (Nat.eqb w 8 && expr_eqb (a_base a) b && Z.eqb (a_off a) k)%bool
                    | _ => false end) (kn ch).
Lemma kw_at_In : forall ch b k, kw_at ch b k = true -> exists v, In (KWord (SA b k) 8 v) (kn ch).
Proof.
intros ch b k H. unfold kw_at in H. apply existsb_exists in H as [K [Hin HK]].
destruct K as [a w v | | | | | | | | | ]; try discriminate HK.
apply andb_prop in HK as [HK H3]. apply andb_prop in HK as [H1 H2].
apply Nat.eqb_eq in H1. apply expr_eqb_eq in H2. apply Z.eqb_eq in H3. subst w.
destruct a as [ab ak]. cbn [a_base a_off] in H2, H3. subst ab ak. exists v. exact Hin.
Qed.
Definition KBLOB_RAND : kentry := KBlob (SA BR 184) (ELit 16) K_RND.
(* LPS 727298f3: the stack write fact (AD2i.KWR_STACK, depth WDEPTH) and the three header words, at every computed
   hand-off state of both CONFIG_RSEQ flags (A/AB01r.v HS_tfib_list_all) *)
Definition stk_chk (ch : acs) : bool :=
  (kn_mem KWR_STACK ch && forallb (kw_at ch eSp0) [0; 8; 16])%bool.
Lemma stk_chk_all : forallb stk_chk HS_tfib_list_all = true.
Proof. vm_compute. reflexivity. Qed.
(* At a hand-off state of flag [r], the knowledge covers the auxv vector and the 16 AT_RANDOM bytes of the flag-r
   layout (YK09.init_kn_with's KUnk over the vector and KBlob over the random bytes, kept to the hand-off), as
   plugin-hostd/fuzz_command's A/StartStkAuxG.v checks them: YK09.AUXSZ r bytes from e_auxb, 16 from e_atrb r. *)
Definition stk_aux_chk (r : Z) (ch : acs) : bool :=
  (kn_vis TFIB ch (fst e_auxb) (snd e_auxb) (AUXSZ r) && kn_vis TFIB ch (fst (e_atrb r)) (snd (e_atrb r)) 16)%bool.
Lemma stk_aux_all :
  (forallb (stk_aux_chk 0) (HS_tfib_list_r 0) && forallb (stk_aux_chk 1) (HS_tfib_list_r 1))%bool = true.
Proof. vm_compute. reflexivity. Qed.
Lemma stk_aux_of : forall b h ch, HS_tfib_r (rseq_z b) h = Some ch -> stk_aux_chk (rseq_z b) ch = true.
Proof.
intros b h ch Hh. pose proof stk_aux_all as H. apply andb_prop in H as [H0 H1].
pose proof (HS_tfib_r_In_r _ h ch Hh) as Hin.
destruct b; cbn [rseq_z] in *; [exact (proj1 (forallb_forall _ _) H1 ch Hin) | exact (proj1 (forallb_forall _ _) H0 ch Hin)].
Qed.
Lemma snd_auxb : snd e_auxb = 24.
Proof. vm_compute. reflexivity. Qed.

Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section t.
(* the binders of PresetD1pA.H_stackup_main_A, in AD2i's Section order *)
Variables (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
Variable SINV : env -> (word -> option byte) -> Prop.
#[local] Notation argH := (YA02.argH0 sp rdraw argv envp
  (in_image_fs inp) (in_stdin inp) uid (in_gid inp) hw (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation entryw := (Z_to_bv 64 (Z.of_N Asan.M.init_pc)).
Hypothesis SINV_sp0 : forall E' M, SINV E' M -> uE E' e_sp0 = TOP + 8388608.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk argv envp
  (in_image_fs inp) (in_stdin inp) uid (in_gid inp) hw (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem inp mbase TPH entryw sp rdraw a.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation HID := (hid TFIB TOP argH E ch model).
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation krs := (kb_rseq (in_kernel inp)).
#[local] Notation RZ := (rseq_z krs).
#[local] Notation ztop := (bv_unsigned (ed_top rdraw)).
#[local] Notation H1 := (AD2i.H1 sp rdraw inp ch E model).
(* the start-up facts this section reads, by the proofs of lib/A/AD2i.v's uS0, ev1, ev2 and ev9 at this
   section's binders *)
Lemma uS0 : u eSp0 = usp.
Proof.
pose proof (SINV_sp0 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as X.
rewrite AD2i.eSp0_e_sp0. unfold YA02.TOP in X. lia.
Qed.
Lemma hev1 : bv_unsigned (ev E 1) = Z.of_nat (length argv).
Proof.
rewrite (HE 1%nat) by (unfold NX0G; lia). cbn. apply u64_lit. pose proof (proj1 Hva). lia.
Qed.
Lemma hev2 : bv_unsigned (ev E 2) = Z.of_nat (length envp).
Proof.
rewrite (HE 2%nat) by (unfold NX0G; lia). cbn. apply u64_lit. pose proof (proj1 Hve). lia.
Qed.
Lemma hev9 : bv_unsigned (ev E 9) = Z.of_nat (block_items argv envp mod 2).
Proof.
rewrite (HE 9%nat) by (unfold NX0G; lia).
change (bv_unsigned (Z_to_bv 64 (Z.of_nat (block_items argv envp mod 2))) = Z.of_nat (block_items argv envp mod 2)).
apply u64_lit. pose proof (YP08.yp_gap_range argv envp). lia.
Qed.

Lemma usp_win : 140735340871680 <= usp <= 140737488355328 /\ usp mod 16 = 0.
Proof. pose proof Hsp as (L & Hh & M). unfold sp_window_lo in L. unfold sp_window_hi in Hh. lia. Qed.
Lemma img_hi_small : 0 <= img_hi TFIB < 2 ^ 32.
Proof. cbn. lia. Qed.

(* R1 half: no byte at or above TOP is hidden by H1 (as plugin-hostd/fuzz_command's A/AD1p.v W1_high_visible) *)
Lemma H1_hi : forall a : word, TOP <= bv_unsigned a -> H1 a = false.
Proof.
intros a Ha. unfold AD2i.H1. cbv beta.
destruct (argH E a) eqn:Hg.
- cbn [negb]. rewrite andb_false_r. reflexivity.
- rewrite YA0j.ho_hid_high; [reflexivity | exact Ha | exact Hg].
Qed.

(* the two hand-off facts, at this hand-off state *)
Lemma chk_parts : kn_mem KWR_STACK ch = true /\ forallb (kw_at ch eSp0) [0; 8; 16] = true.
Proof.
pose proof (proj1 (forallb_forall _ _) stk_chk_all ch (HS_tfib_r_In _ h ch Hch)) as H. unfold stk_chk in H.
apply andb_prop in H as [A B]. exact (conj A B).
Qed.

Lemma MR_full : forall x : word, MR x <> None -> FULL x <> None.
Proof. intros x H. unfold Mr, mrestrict in H. destruct (HID x); [exfalso; exact (H eq_refl) | exact H]. Qed.
Lemma off_hull : forall x : Z, img_hi TFIB <= x < 2 ^ 64 -> find_segment TSEGS (bv_unsigned (Z_to_bv 64 x)) 1 = None.
Proof.
intros x Hx. apply tfib_in_hull. unfold APSG.in_hull. rewrite u64_lit by (pose proof img_hi_small; lia).
apply andb_false_intro2. apply Z.ltb_ge. lia.
Qed.
Lemma mbyte_full : forall x : Z, img_hi TFIB <= x < 2 ^ 64 -> mbyte TSEGS MR x <> None -> FULL (Z_to_bv 64 x) <> None.
Proof.
intros x Hx H. apply MR_full. unfold mbyte in H. destruct (MR (Z_to_bv 64 x)) eqn:E1; [discriminate|].
rewrite (seg_rom_none_of_find TSEGS _ (off_hull x Hx)) in H. exact H.
Qed.
Lemma wview_full : forall x : Z, img_hi TFIB <= x < 2 ^ 64 -> wview TSEGS MR (Z_to_bv 64 x) <> None -> FULL (Z_to_bv 64 x) <> None.
Proof.
intros x Hx Hw. apply MR_full. unfold wview in Hw. destruct (MR (Z_to_bv 64 x)); [discriminate|].
rewrite (off_hull x Hx) in Hw. exact Hw.
Qed.
Lemma store1_wview : forall m (a : word), RiscvSemantics.store_ok TSEGS m a 1 = true -> wview TSEGS m a <> None.
Proof. intros m a H. cbn [RiscvSemantics.store_ok] in H. destruct (wview TSEGS m a); [discriminate | discriminate H]. Qed.

(* [usp - WDEPTH, usp): the KWr *)
Lemma present_low : forall a, usp - WDEPTH <= a < usp -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha. pose proof chk_parts as (K & _). unfold KWR_STACK in K.
pose proof usp_win as ((U1 & U2) & _). pose proof img_hi_small as Hih.
pose proof (ho_wr TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ K) as W.
assert (Hst : estart E (SA eSp0 (- WDEPTH)) = usp - WDEPTH).
{ unfold estart. cbn [a_base a_off]. pose proof uS0 as U. unfold uE in U. lia. }
assert (Hl : elenZ E (ELit WDEPTH) = WDEPTH) by (unfold elenZ; cbn [edenot]; apply u64_lit; unfold WDEPTH; lia).
rewrite Hst, Hl in W. specialize (W (a - (usp - WDEPTH)) 1%nat ltac:(lia) ltac:(lia)).
replace (usp - WDEPTH + (a - (usp - WDEPTH))) with a in W by lia.
apply wview_full; [unfold WDEPTH in *; lia|]. exact (store1_wview _ _ W).
Qed.

(* a KWord of width 8 in the hand-off kn *)
Lemma present_kw : forall b k, kw_at ch b k = true ->
  forall x, u b + k <= x < u b + k + 8 -> img_hi TFIB <= x < 2 ^ 64 -> FULL (Z_to_bv 64 x) <> None.
Proof.
intros b k Hk x Hx Hb. destruct (kw_at_In ch b k Hk) as [v Hin].
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ Hin) as KO.
cbn [kentry_ok] in KO. destruct KO as (_ & _ & Hr).
assert (Ea : adenot E (SA b k) = Z_to_bv 64 (u b + k)) by reflexivity. rewrite Ea in Hr.
apply (proj1 (rdn_mbytes TSEGS MR 8 (u b + k) _)) in Hr as [Hl Hm].
specialize (Hm (Z.to_nat (x - (u b + k))) ltac:(lia)). rewrite Z2Nat.id in Hm by lia.
replace (u b + k + (x - (u b + k))) with x in Hm by lia.
apply mbyte_full; [exact Hb|]. rewrite Hm.
destruct (nth_error _ _) eqn:N; [discriminate|]. apply nth_error_None in N. rewrite Hl in N. lia.
Qed.

(* The values of the start state's auxv and AT_RANDOM base expressions at the hand-off: the auxv vector starts at
   usp + 8 argc + 8 envc + 24, the random bytes at usp + C - 16, C the model's block_head_size at the run's own
   CONFIG_RSEQ flag (the proofs of plugin-hostd/fuzz_command's A/AD2i.v u_auxb / u_atrb, over AD2i's ev lemmas).
   [bv_wrap], [u_add64] and [u_mul64] are [mod]s, so [lia] needs the euclidean division equations in split_lit_val,
   u_e_auxvE and u_e_atrandomE (as there). *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma split_lit_val : forall e, 0 <= snd (split_lit e) -> snd (split_lit e) <= u e ->
  u (fst (split_lit e)) + snd (split_lit e) = u e.
Proof.
intros e. destruct (split_lit e) as [b k] eqn:Hs. cbn [fst snd]. intros Hk Hle.
pose proof (split_lit_denot E e b k Hs) as D. unfold uE in *. rewrite D in Hle |- *.
rewrite Z_to_bv_unsigned in Hle |- *. pose proof (YK11.u64_range (edenot E b)) as Rb.
unfold bv_wrap, bv_modulus in *. change (2 ^ Z.of_N 64) with (2 ^ 64) in *. lia.
Qed.
Lemma u_e_sp0E : u e_sp0 = usp.
Proof. rewrite <- AD2i.eSp0_e_sp0. exact uS0. Qed.
Lemma u_e_auxvE : u e_auxv = usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24.
Proof.
pose proof (proj1 Hsp) as L0. pose proof (proj1 (proj2 Hsp)) as L1. unfold sp_window_lo, sp_window_hi in L0, L1.
pose proof (proj1 Hva). pose proof (proj1 Hve).
assert (U3 : bv_unsigned (edenot E (EVar V_ARGC)) = Z.of_nat (length argv)) by exact hev1.
assert (U4 : bv_unsigned (edenot E (EVar V_ENVC)) = Z.of_nat (length envp)) by exact hev2.
pose proof u_e_sp0E as US.
unfold e_auxv, e_envp, eadd, escale, uE in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite US, U3, U4.
rewrite !Z.mod_small by lia. lia.
Qed.
Lemma u_e_atrandomE : u (e_atrandom RZ)
  = usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24 + AUXSZ RZ + 8 * Z.of_nat (block_items argv envp mod 2).
Proof.
pose proof (proj1 Hsp) as L0. pose proof (proj1 (proj2 Hsp)) as L1. unfold sp_window_lo, sp_window_hi in L0, L1.
pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (rseq_z_range krs).
pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)).
assert (UG : bv_unsigned (edenot E (EVar V_G)) = Z.of_nat (block_items argv envp mod 2)) by exact hev9.
pose proof u_e_auxvE as UA.
unfold e_atrandom, eadd, eaddz, escale, uE, AUXSZ in *. rewrite !mkAlu_denot, !mkMd_denot, !edenot_lit.
rewrite !u_add64, !u_mul64, !u64_lit by lia. rewrite UA, UG.
rewrite !Z.mod_small by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Lemma u_auxb : u (fst e_auxb) + snd e_auxb = usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24.
Proof.
pose proof u_e_auxvE as UA. pose proof (proj1 Hsp) as L0. unfold sp_window_lo in L0.
assert (Hk : snd e_auxb = 24) by (vm_compute; reflexivity).
unfold e_auxb. rewrite split_lit_val; [exact UA | fold e_auxb; rewrite Hk; lia | fold e_auxb; rewrite Hk, UA; lia].
Qed.
Lemma u_atrb : u (fst (e_atrb RZ)) + snd (e_atrb RZ) = usp + Z.of_nat (block_head_size krs argv envp) - 16.
Proof.
pose proof u_e_atrandomE as UR. pose proof (proj1 Hsp) as L0. unfold sp_window_lo in L0.
pose proof (AUXSZ_of krs) as HA. unfold AUXSZ in HA, UR.
assert (Hk : snd (e_atrb RZ) = 24 + AUXSZ RZ) by (destruct (kb_rseq (in_kernel inp)); vm_compute; reflexivity).
unfold AUXSZ in Hk. pose proof (rseq_z_range krs).
unfold e_atrb. rewrite split_lit_val.
- rewrite UR. unfold block_head_size. cbv zeta. rewrite ?Nat2Z.inj_add, ?Nat2Z.inj_mul.
  assert (Hbi : Z.of_nat (block_items argv envp) = Z.of_nat (length argv) + Z.of_nat (length envp) + 3)
  by (unfold block_items; lia).
  lia.
- fold (e_atrb RZ). rewrite Hk. lia.
- fold (e_atrb RZ). rewrite Hk, UR. lia.
Qed.
(* A byte a known region covers, above the image, is present (plugin-hostd/fuzz_command's A/StartStkAuxG.v) *)
Lemma vis_present : forall rb rk len, kn_vis TFIB ch rb rk len = true -> forall i, 0 <= i < len ->
  img_hi TFIB <= u rb + rk + i < 2 ^ 64 -> FULL (Z_to_bv 64 (u rb + rk + i)) <> None.
Proof.
intros rb rk len Hv i Hi Hr.
pose proof (ho_vis_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) tfib_in_hull tfib_hull_ok E ch R FULL model HC rb rk len Hv i Hi) as Hh.
unfold hreader, mbyte in Hh.
destruct (MR (Z_to_bv 64 (u rb + rk + i))) as [bb|] eqn:Em.
- rewrite (ho_Mr_full _ _ _ _ _ _ _ _ _ Em). discriminate.
- rewrite (seg_rom_none_of_find TSEGS _ (off_hull _ Hr)) in Hh. exfalso. apply Hh. reflexivity.
Qed.
(* the auxv vector: [usp + 8 argc + 8 envc + 24, + 432 + 32 RZ) *)
Lemma present_aux : forall a,
  usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24 <= a
  < usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 456 + 32 * RZ ->
  a < 2 ^ 64 -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha H64. pose proof (stk_aux_of krs h ch Hch) as Hchk. apply andb_prop in Hchk as [HA _].
pose proof u_auxb as UA. pose proof usp_win as ((U1 & U2) & _). pose proof img_hi_small as Hih.
replace a with (u (fst e_auxb) + snd e_auxb + (a - (u (fst e_auxb) + snd e_auxb))) by lia.
apply (vis_present _ _ _ HA); unfold AUXSZ; lia.
Qed.
(* the AT_RANDOM bytes: [usp + C - 16, usp + C) *)
Lemma present_rand : forall a,
  usp + Z.of_nat (block_head_size krs argv envp) - 16 <= a < usp + Z.of_nat (block_head_size krs argv envp) ->
  a < 2 ^ 64 -> FULL (Z_to_bv 64 a) <> None.
Proof.
intros a Ha H64. pose proof (stk_aux_of krs h ch Hch) as Hchk. apply andb_prop in Hchk as [_ HR].
pose proof u_atrb as UR. pose proof usp_win as ((U1 & U2) & _). pose proof img_hi_small as Hih.
replace a with (u (fst (e_atrb RZ)) + snd (e_atrb RZ) + (a - (u (fst (e_atrb RZ)) + snd (e_atrb RZ)))) by lia.
apply (vis_present _ _ _ HR); lia.
Qed.

(* [usp + 24, ztop): an argH0 byte, an auxv word or an AT_RANDOM byte (YA02.argH0_false_cases at this input) *)
Lemma argH_in : forall x, usp + 24 <= x < ztop -> argH E (Z_to_bv 64 x) = true \/
  (usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 24 <= x
   < usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + 456 + 32 * RZ)
  \/ (usp + Z.of_nat (block_head_size krs argv envp) - 16 <= x < usp + Z.of_nat (block_head_size krs argv envp)).
Proof.
intros x Hx. pose proof usp_win as ((U1 & U2) & _). pose proof (u64_range (ed_top rdraw)) as RT.
destruct (argH E (Z_to_bv 64 x)) eqn:Hg; [left; reflexivity | right].
(* [YA02.argH0_false_cases]'s own proof at this input: its exported binder list leads with section variables this
   file does not hold ("sp" given where a segment list is expected), as plugin-hostd/fuzz_reply's A/AStkCov.v *)
unfold YA02.argH0, YA02.argH0_core in Hg. cbv zeta in Hg.
cbn [in_kernel YA02.inp recorded_kernel kb_rseq] in Hg.
rewrite u64_lit in Hg by lia.
repeat rewrite orb_false_iff in Hg.
destruct Hg as ((((J1 & J2) & Jt) & J5) & Jp).
apply andb_false_iff in J1, J2, Jt, J5, Jp.
destruct J1 as [J1|J1], J2 as [J2|J2], Jt as [Jt|Jt], J5 as [J5|J5], Jp as [Jp|Jp];
  rewrite ?Z.leb_gt, ?Z.ltb_ge in J1; rewrite ?Z.leb_gt, ?Z.ltb_ge in J2; rewrite ?Z.leb_gt, ?Z.ltb_ge in Jt;
  rewrite ?Z.leb_gt, ?Z.ltb_ge in J5; rewrite ?Z.leb_gt, ?Z.ltb_ge in Jp; lia.
Qed.
(* an argH byte has its entry-image value, and the image runs from sp to the stack VMA's end (the launch premise;
   plugin-hostd/fuzz_command's A/AD1p.v wrap_mem_present) *)
Lemma wrap_some : forall x, usp <= x < ztop -> x < 2 ^ 64 ->
  wrap_mem inp mbase TPH entryw sp rdraw (Z_to_bv 64 x) <> None.
Proof.
intros x Hx H64. pose proof (u64_range sp) as RS.
pose proof (length_entry_stack_image_launch Sv48 inp mbase TPH entryw sp brk rdraw Hlau) as HLEN.
rewrite (wrap_above_sp inp mbase TPH entryw sp rdraw (Z_to_bv 64 x)) by (rewrite u64_lit by lia; lia).
unfold stack_to_mem. rewrite u64_lit by lia.
replace (bv_unsigned sp <=? x) with true by (symmetry; apply Z.leb_le; lia).
cbv zeta.
replace (x - bv_unsigned sp <? Z.of_nat (length (entry_stack_image inp mbase TPH entryw sp rdraw))) with true
by (symmetry; apply Z.ltb_lt; lia).
intros Hn. apply nth_error_None in Hn. lia.
Qed.
(* the stack VMA's end: a page boundary at or above the entry sp (entry_launch_ok_va) *)
Lemma block_le_page : usp <= ztop /\ ztop mod 4096 = 0.
Proof.
pose proof (length_entry_stack_image_launch Sv48 inp mbase TPH entryw sp brk rdraw Hlau) as HLEN.
pose proof (Nat2Z.is_nonneg (length (entry_stack_image inp mbase TPH entryw sp rdraw))) as H0.
pose proof Hlau as ((T & _) & _). unfold page_size in T. split; [lia | exact T].
Qed.
(* a page-aligned ly_top within top_ok of usp (at most usp + 3920) is at or below that end *)
Lemma ly_le_page : forall ly : alayout, ly_top ly mod 4096 = 0 -> AD1v.top_ok (rc := rc) usp ly ->
  ly_top ly <= ztop.
Proof.
intros ly Hal ((_ & Htop) & _). pose proof block_le_page as (Hle & Hal2).
pose proof (Z.div_mod (ly_top ly) 4096 ltac:(lia)) as DT. pose proof (Z.div_mod ztop 4096 ltac:(lia)) as DZ.
rewrite Hal, Z.add_0_r in DT. rewrite Hal2, Z.add_0_r in DZ. lia.
Qed.

(* THE MAIN-ENTRY PRESENCE LEMMA (A'): with ly_top page aligned and within top_ok of usp (AD1v.top_ok; AD1g.uTop and
   AD1f.tfib_top_ok for AD1g.ly0), every byte of [usp - 64 KiB, ly_top) is present in H1 / FULL at main's entry. *)
Theorem stack_up_main_A : forall ly : alayout, ly_top ly mod 4096 = 0 -> AD1v.top_ok (rc := rc) usp ly ->
  forall a, usp - 65536 <= a < ly_top ly -> apresent H1 FULL a.
Proof.
intros ly Hal Htop a Ha.
pose proof usp_win as ((U1 & U2) & _). pose proof img_hi_small as Hih.
pose proof (ly_le_page ly Hal Htop) as Hpg. pose proof Htop as ((_ & Htop') & _).
assert (H64 : a < 2 ^ 64) by lia.
split.
- apply H1_hi. rewrite u64_lit by lia. unfold YA02.TOP. lia.
- assert (HP : FULL (Z_to_bv 64 a) <> None).
  { destruct (Z_lt_le_dec a usp) as [C0|C0].
    { apply present_low. unfold WDEPTH. lia. }
    destruct (Z_lt_le_dec a (usp + 24)) as [C1|C1].
    { pose proof chk_parts as (_ & KH). cbn [forallb] in KH.
      apply andb_prop in KH as [K0 KH]. apply andb_prop in KH as [K8 KH]. apply andb_prop in KH as [K16 _].
      pose proof uS0 as U.
      destruct (Z_lt_le_dec a (usp + 8)); [|destruct (Z_lt_le_dec a (usp + 16))].
      - apply (present_kw eSp0 0 K0); lia.
      - apply (present_kw eSp0 8 K8); lia.
      - apply (present_kw eSp0 16 K16); lia. }
    destruct (argH_in a ltac:(lia)) as [Hg | [Hx | Hx]].
    + rewrite (HM _ Hg). apply wrap_some; lia.
    + apply present_aux; lia.
    + apply present_rand; lia. }
  destruct (FULL (Z_to_bv 64 a)) as [b|] eqn:Hb; [exists b; reflexivity | exfalso; exact (HP eq_refl)].
Qed.

(* the same at the driver's world W1 (w_H W1 = H1) *)
Hypothesis H1_8 : forall a : Z, YG0f.in_band_rw a -> H1 (Z_to_bv 64 a) = H1 (Z_to_bv 64 (a - a mod 8)).
Corollary stack_up_main_W1_A : forall ly : alayout, ly_top ly mod 4096 = 0 -> AD1v.top_ok (rc := rc) usp ly ->
  forall a, usp - 65536 <= a < ly_top ly -> apresent (w_H (AD2i.W1 sp rdraw inp Hsp Hva ch E model H1_8)) FULL a.
Proof. exact stack_up_main_A. Qed.
End t.
End g.
