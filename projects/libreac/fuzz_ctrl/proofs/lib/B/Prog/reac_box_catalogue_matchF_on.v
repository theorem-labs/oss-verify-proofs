(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 3060 of its 3101 lines of code are new or changed and 207 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/reac_box_catalogue_match.v, with its module paths, module names, addresses and numbers changed; 3183 of its 3895 lines of code are new or changed and 2389 lines of the source are left out. *)
(* lib/B/Prog/reac_box_catalogue_matchF_on.v -- route (C) phase 2, image B: the ADDITIVE `_on` copy of the accepted
   footprint run lib/B/Prog/reac_box_catalogue_matchF.v (not in this delivery) (which stays byte-identical), generated from it by the patch
   list of gen_matchF_on.py (sha256 7498e0f9eb10; internal record).  A Theorem Labs lane,
   2026-10-29.  It proves reac_box_catalogue_match_contract_F_on (reac_box_catalogue_match_c.v, the route-(C) block)
   from the four callees' `_on` footprint contracts, each cited BY NAME:
     asan_stack_malloc_2_contract_F_on   lib/B/Prog/asan_stack_malloc_cF_on.v, the ONE hypothesis HSM2 of Section
                                         Callees (no local copy; its helpers fs_shadow_area / IMG_HI are the leaf's
                                         asan_stack_malloc_cF.v / ImgBounds.v ones)
     reac_ctrl_parse_contract_F_on       lib/B/Prog/reac_ctrl_parse_c.v
     reac_box_model_block_contract_F_on  lib/B/Prog/reac_box_model_block_cF_on.v
     bcmp_wrap_contract_F_on             lib/B/Prog/bcmp_wrap_c_on.v
   The Sections, the lemma names and the scripts are the accepted file's; only where shadow_rw enters is changed:
   - the Section hypothesis SR : shadow_rw m becomes SRo : shadow_rw_on R m with R := reac_box_catalogue_match_shadow_R
     f len Sp FS (notation cmR); nothing widens it back to a universal shadow_rw;
   - the invariant's runtime part RT (so cmJ / cmInv) and the release state cmAtRel carry cmSRT mc := forall P,
     shadow_rw_on P m -> shadow_rw_on P mc in place of shadow_rw mc: R at mc is cmSRT_R; the run's own stores keep it
     (cm_shadow_rw_write), a run that keeps every byte writable and readable keeps it (shadow_rw_mono, also across
     __asan_stack_malloc_2, whose post has no shadow fact), a callee's forall-P post carries it (cmSRT_step); cmPost,
     cm_mb_post and cm_parse_post have the forall-P conjunct of the contract / callee posts;
   - each callee is fed its own region by shadow_rw_on_mono with a Theorem Labs lane's inclusion lemmas
     (reac_box_catalogue_matchF_onIncl.v): cmOn_R_malloc, cmOn_R_parse, cmOn_R_mb, cmOn_R_bcmp (__asan_stack_malloc_2's
     region is carried over the prologue's window writes by a Theorem Labs lane's B.ShadowRwOnK.fl_shadow_rw_on); the frame's own
     shadow bytes (fk_facts, the header, the marks, the exits) are in R by cmOn_R_fr, the callee windows and class
     blocks that cm_cf_rd re-reads by cmOn_R_win / cmOn_R_area;
   - cm_mb takes 50 <= len (R holds the table's shadow under that guard; its one caller cm_rows holds the gate).
   rule 24: route-(C) proof work on this lane's own accepted run; At ossv/recipes c5e779efe8c (2026-10-31), no released proof of it exists outside this unit. *)
(* This delivery then edited comment text only: the code is unchanged from release c5e779efe8c, the comments are not. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes
  ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* StepF after Step: its step / if_* / store_done (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
(* Route (C): the region form (ShadowRwOn), the callees' _on contracts and regions (cited by name), ImgBounds (the
   IMG_LO / IMG_HI of asan_stack_malloc_cF.v's text), and a Theorem Labs lane's region-inclusion lemmas. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOnK.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ImgBounds sh_word_on asan_stack_malloc_c_on
  asan_stack_malloc_cF asan_stack_malloc_cF_on reac_box_model_block_c_on reac_box_model_block_cF_on bcmp_wrap_c_on
  reac_box_catalogue_matchF_onIncl.
(* The plain proof last: its lemmas outside the Section (the table, the footprint and shadow facts), with the names it
   resolves; it exports neither Step nor StepF. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_catalogue_match.
Import ListNotations.
Open Scope Z_scope.


(* ------------------------------------------------------------------------------------------------------------ *)
(* The callee contracts are cited BY NAME (route (C)); the class-2 stack malloc's is Section Callees' one hypothesis. *)

Section Callees.


(* Route (C): __asan_stack_malloc_2's footprint contract in its region form, cited BY NAME from its leaf
   lib/B/Prog/asan_stack_malloc_cF_on.v (asan_stack_malloc_2_contract_F_on = asan_stack_malloc_contract_F_on 2
   ASAN_STACK_MALLOC_2 ASAN_STACK_MALLOC_K: premise shadow_rw_on (asan_stack_malloc_shadow_R FS 2) m, no shadow fact in
   its post).  No local copy: the accepted file's LOCAL COPY asan_stack_malloc_contract_F and its two helpers
   fs_shadow_area / IMG_HI are the leaf's asan_stack_malloc_cF.fs_shadow_area and ImgBounds.IMG_HI here. *)
Hypothesis HSM2 : asan_stack_malloc_2_contract_F_on.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Footprint tools.                                                                                              *)

(* a Theorem Labs lane's finding: StepF's alia has no Euclidean equations, so a shadow access x / 8 + off is not closed by the
   default solve_acc branches.  acc_hint first tries the rng hypothesis whose start has the access's leftmost term
   (plain lia, x / 8 an atom), then every rng hypothesis with Z.div_mod_to_equations; lia. *)
Ltac acc_close_with H :=
  lazymatch goal with
  | |- acc_in ?RG (Z_to_bv 64 ?E, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | rng RG ?lo ?len =>
          apply (rng_acc_litZ' RG lo len E n nz H (@eq_refl Z nz) (@eq_refl bool true));
          Z.div_mod_to_equations; lia
      end
  | |- acc_in ?RG (?a, ?n) =>
      let nz := eval cbv in (Z.of_nat n) in
      lazymatch type of H with
      | rng RG ?lo ?len =>
          apply (rng_acc_varZ RG lo len a n nz H (@eq_refl Z nz));
          Z.div_mod_to_equations; lia
      end
  end.
Local Ltac acc_hint ::=
  lazymatch goal with
  | |- acc_in ?RG (?a, ?n) =>
      let E := addr_expr a in
      lazymatch E with
      | context[Z.div _ _] =>
          first [ let X := leftmost E in
                  match goal with
                  | H : rng RG ?lo _ |- _ => let Y := leftmost lo in constr_eq X Y; solve_acc_with H
                  end
                | match goal with H : rng RG _ _ |- _ => acc_close_with H end ]
      end
  end.

(* The store hook of this file: Tac.v's mem_after_store_opt (the hook reac_box_catalogue_match.v runs under) on evtF
   goals, as d0b3606c9c9 lib/B/Prog/reac_ctrl_parseF.v's rcpF_store_opt.  It folds Z_to_le_bytes of a literal into
   le8 / le4 / le2 / le1 as Tac's fix_lit_store does, and it does not run StepF's norm_lit_store_bytes, whose
   le1 (Z_to_bv 64 z) -> [Z_to_bv 8 z] folding would change the stored bytes the plain script names. *)
Ltac cmF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac cmF_store_opt :=
  try cmF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= cmF_store_opt.

(* A part of a shadow word cover is a shadow word cover; the shadow byte of one of its bytes is in it. *)
Lemma shc_sub : forall RG p n p' n', p <= p' -> 0 < n' -> p' + n' <= p + n -> sh_cover RG p n -> sh_cover RG p' n'.
Proof.
  intros RG p n p' n' H1 H2 H3 H. unfold sh_cover, shadow_addr in *.
  apply (rng_sub' RG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

Lemma shc_byte : forall RG p n X, p <= X < p + n -> sh_cover RG p n -> rng RG (X / 8 + ASAN_K) 1.
Proof.
  intros RG p n X HX H. unfold sh_cover, shadow_addr in H.
  apply (rng_sub' RG _ _ _ _ H). Z.div_mod_to_equations; lia.
Qed.

(* A shadow word cover inside a range [L, H) of shadow bytes. *)
Lemma shc_in : forall RG L H p n, rng RG L (H - L) -> L <= shadow_addr p / 8 * 8 ->
  shadow_addr (p + n - 1) / 8 * 8 + 8 <= H -> sh_cover RG p n.
Proof. intros RG L H p n R H1 H2. unfold sh_cover. apply (rng_sub' RG L (H - L) _ _ R). lia. Qed.

(* The cells of asan_tls_cells that __asan_stack_malloc_c's text names one by one. *)
Lemma tls_rngs : forall RG TP DT TS C T DB k,
  Forall (fun iv => rng RG (fst iv) (snd iv - fst iv)) (fp_tls TP DT TS C T DB k) ->
  rng RG (TP - 8) 24 /\ rng RG (bv_unsigned DT + 8) 8 /\ rng RG (TP - 88) 8 /\ rng RG (bv_unsigned TS + 8 * k) 8 /\
  rng RG (bv_unsigned C + 152) 8 /\ rng RG (bv_unsigned T + 48) 16 /\ rng RG (bv_unsigned DB + 24) 8.
Proof.
  intros RG TP DT TS C T DB k H. cbn [fp_tls] in H.
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R1 H]. apply Forall_cons_iff in H as [R2 H].
  apply Forall_cons_iff in H as [_ H]. apply Forall_cons_iff in H as [_ H].
  apply Forall_cons_iff in H as [R3 H]. apply Forall_cons_iff in H as [R4 H].
  apply Forall_cons_iff in H as [R5 H]. apply Forall_cons_iff in H as [R6 H].
  do 5 (apply Forall_cons_iff in H as [_ H]).
  apply Forall_cons_iff in H as [R7 _].
  cbn [fst snd] in R1, R2, R3, R4, R5, R6, R7.
  split; [apply (rng_sub RG _ _ _ _ R1); lia|]. split; [apply (rng_sub RG _ _ _ _ R2); lia|].
  split; [apply (rng_sub RG _ _ _ _ R3); lia|]. split; [apply (rng_sub RG _ _ _ _ R4); lia|].
  split; [apply (rng_sub RG _ _ _ _ R5); lia|]. split; [apply (rng_sub RG _ _ _ _ R6); lia|].
  apply (rng_sub RG _ _ _ _ R7); lia.
Qed.

(* The class-c frame area of the side stack spans 2^20 bytes from fs_frame FS c 0 (c <= 2), its shadow 2^17. *)
Lemma fs_frame_span : forall FS0 c, (c <= 2)%nat ->
  fs_frame FS0 c (fs_M c) = fs_frame FS0 c 0 + 1048576 /\ fs_shadow_area c = 131072 /\
  fs_frame FS0 c 0 = FS0 + 36864 + Z.of_nat c * 1048576.
Proof.
  intros FS0 c Hc. unfold fs_frame. change (2 ^ 20) with 1048576.
  destruct c as [|[|[|c]]]; [| | | lia].
  - change (fs_M 0) with 16384. change (fs_B 0) with 64. split; [lia|]. split; [reflexivity | lia].
  - change (fs_M 1) with 8192. change (fs_B 1) with 128. split; [lia|]. split; [reflexivity | lia].
  - change (fs_M 2) with 4096. change (fs_B 2) with 256. split; [lia|]. split; [reflexivity | lia].
Qed.

(* The shadow checks of this build, over StepF (the plain file's two Ltacs, on evtF goals). *)
Ltac steps_until_if :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step; steps_until_if
  | _ => idtac
  end.

Ltac bjoin G r := lazymatch goal with |- evtF _ _ _ (MS ?R _ _ _ _ _ _) => exact (G (reg_get R r)) end.

(* ============================ the run ============================ *)

Section MatchF.
Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (RNG : ExecF.footprint).
(* Route (C): the run's own region R (reac_box_catalogue_match_c.v, the route-(C) block). *)
Local Notation cmR := (reac_box_catalogue_match_shadow_R f len Sp FS).
Hypothesis HPC : reac_ctrl_parse_contract_F_on.
Hypothesis HMB : reac_box_model_block_contract_F_on.
Hypothesis HBC : bcmp_wrap_c_on.bcmp_wrap_contract_F_on.
Hypothesis Rf : 0 <= f < 2^64.
Hypothesis Rlen : 0 <= len < 2^64.
Hypothesis RS : Sp < 2^64.
Hypothesis S16 : Sp mod 16 = 0.
Hypothesis HK : 9136 <= Sp.
Hypothesis ST : stk rsegs m (Sp - 9136) Sp.
Hypothesis Hfb : length fb = 50%nat.
Hypothesis HF : 50 <= len -> 0 < f /\ f + 50 <= 2^64 /\ bytes_at rsegs m f fb /\ (f + 50 <= Sp - 9136 \/ Sp <= f).
Hypothesis MI : mem_inv rsegs m.
Hypothesis AC : asan_cells m.
Hypothesis SRo : shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) m.
Hypothesis HHM : HIGHMEM_BEG <= Sp - 9136.
Hypothesis HAE : Sp <= APPMEM_END.
Hypothesis AW : addressable m (Sp - 9136) 9136.
Hypothesis AFU : 50 <= len -> addressable m f 50 /\ app_mem (f + 50).
Hypothesis AT : addressable m CM_T 3256.
Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
Hypothesis HGOT : bytes_at rsegs m GOT_CF (le8 (wa CF)).
Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Hypothesis FP0 : fp [0%nat; 1%nat; 2%nat] m (bv_unsigned tp) FS (Sp - 9136) Sp
  (reac_box_catalogue_match_W Sp) (reac_box_catalogue_match_D f len).
Hypothesis TLS0 : reac_box_catalogue_match_tls m (bv_unsigned tp) FS (Sp - 9136) Sp.
(* The footprint premises, in the forms the proof uses: the shadow word covers of f, T and BC quantified (a ground
   rng premise with divisions in its bounds would slow every lia of the Section). *)
Hypothesis RB : rng_bytes RNG.
Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
Hypothesis RWIN : rng RNG (Sp - 9136) 9136.
Hypothesis RWSH : rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)).
Hypothesis RFD : 50 <= len -> rng RNG f 50.
Hypothesis RFW : 50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n.
Hypothesis RTB : rng RNG CM_T 3256.
Hypothesis RTW : forall p n, CM_T <= p -> 0 < n -> p + n <= CM_T + 3256 -> sh_cover RNG p n.
Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
Hypothesis RBCW : sh_cover RNG REAC_CTRL_PARSE_BC 6.
Hypothesis RHDR : rng RNG FS (fs_frame FS 0 0 - FS).
Hypothesis RFPW : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS).
Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells m (bv_unsigned tp) DT TS C T DB k ->
  Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).

Definition aWf : list ivl := [(Sp - 9136, Sp)].
Definition aDf : list ivl := if len <? 50 then [] else [(f, f + 50)].
Definition aXs : list ivl := fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (Sp - 9136), shadow_addr Sp)].
Definition aWc : list ivl := (Sp - 9136, Sp) :: aXs.

Definition aTL (mc : word -> option byte) : Prop :=
  forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
    fp_dj (fp_tls (bv_unsigned tp) DT TS C T DB kk) aXs.

(* The side stack's place and the data ranges apart from the class-0/1/2 side-stack bytes (fp in m). *)
Lemma acl_fs : 0 < FS /\ FS mod 4096 = 0 /\ ASAN_GT <= FS /\ FS + FS_SIZE <= Sp - 9136 /\
  (forall a, FS <= a < FS + FS_SIZE -> app_mem a) /\ fp_dj aDf (fp_w [0%nat; 1%nat; 2%nat] FS).
Proof.
  destruct FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & _) & _ & _ & _ & HFS & HAPP & _ & HDd).
  unfold reac_box_catalogue_match_D in HDd. fold aDf in HDd.
  repeat split; assumption.
Qed.

Lemma acl_out_fpw_d : forall a b x, In (a, b) aDf -> a <= x < b -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros a b x Hin Hx. destruct acl_fs as (_ & _ & _ & _ & _ & DJ). exact (fl_dj_out_r _ _ a b x DJ Hin Hx).
Qed.

Lemma acl_out_fpw_hi : forall x, FS + FS_SIZE <= x -> app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros x Hx Hap. destruct acl_fs as (P1 & P2 & P3 & P4 & P5 & _).
  apply fpw3_out_hi; [exact P2 | exact P1 | clear -P4 HAE; lia | clear -Hx; lia | exact Hap].
Qed.

Lemma acl_out_fpw_lo : forall x, x < FS -> app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x.
Proof.
  intros x Hx Hap. destruct acl_fs as (P1 & P2 & P3 & P4 & P5 & _).
  apply fpw3_out_lo; [exact P1 | clear -P4 HAE; lia | exact Hx | exact Hap].
Qed.

Lemma acl_out_fpw_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  outside (fp_w [0%nat; 1%nat; 2%nat] FS) (shadow_addr x).
Proof.
  intros x Hap Ho. destruct acl_fs as (P1 & P2 & P3 & P4 & P5 & _).
  apply fpw3_out_sh; [exact P2 | exact P1 | clear -P4 HAE; lia | exact P5 | exact Hap | exact Ho].
Qed.

Lemma acl_out_Xs_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  (x < Sp - 9136 \/ Sp <= x) -> outside aXs (shadow_addr x).
Proof.
  intros x Hap Ho Hx. unfold aXs. apply fl_out_app; [exact (acl_out_fpw_sh x Hap Ho)|].
  cbn [outside]. split; [|exact I].
  apply acl_win_sh; [apply acl_S_mod8; [exact S16 | reflexivity] | clear -Hx; lia].
Qed.

Lemma acl_out_Wc_sh : forall x, app_mem x -> outside (fp_w [0%nat; 1%nat; 2%nat] FS) x ->
  (x < Sp - 9136 \/ Sp <= x) -> outside aWc (shadow_addr x).
Proof.
  intros x Hap Ho Hx. pose proof (rt_app_shadow x Hap) as Hs. unfold aWc. cbn [outside].
  split; [clear -Hs HHM; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *; lia|].
  exact (acl_out_Xs_sh x Hap Ho Hx).
Qed.

Lemma acl_out_Wc : forall x, app_mem x -> (x < Sp - 9136 \/ Sp <= x) ->
  outside (fp_w [0%nat; 1%nat; 2%nat] FS) x -> outside aWc x.
Proof.
  intros x Hap H3 H4. unfold aWc, aXs. cbn [outside].
  split; [clear -H3; lia|].
  apply fl_out_app; [exact H4|]. cbn [outside]. split; [|exact I].
  apply acl_sh_out; [exact Hap | clear -HK; lia | exact HAE].
Qed.

(* The shadow byte of fr + 8 i is i above the shadow byte of fr. *)
Lemma cm_sh_add8 : forall fr i, fr mod 8 = 0 -> shadow_addr (fr + 8 * i) = shadow_addr fr + i.
Proof. intros fr i Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

(* The aligned frame pointer: sp after andi sp, (sp - 128), -32. *)
Definition CA : Z := (Sp - 128) / 32 * 32.

Lemma CA_facts : CA mod 32 = 0 /\ Sp - 144 <= CA <= Sp - 128.
Proof. unfold CA. pose proof S16 as H16. Z.div_mod_to_equations. lia. Qed.

(* The 192-byte class-2 frame: real (fr = CA - 192, body sp = CA - 192) or a side-stack frame fs_frame FS 2 jj
   (body sp = CA). *)
Definition cmFK (fr sp2 jj nn : Z) : Prop :=
  (fr = CA - 192 /\ sp2 = CA - 192 /\ jj = 0 /\ nn = 0) \/
  (0 <= jj < fs_M 2 /\ fr = fs_frame FS 2 jj /\ sp2 = CA /\ nn = 1).

(* ---- Route (C): the transport of the run's shadow facts, and the frame's place in R ---- *)

(* Every shadow region the entry memory m holds, mc holds: the contract's forall-P post at mc.  The invariant carries it
   in place of the accepted run's universal shadow_rw mc; R at mc follows from SRo (cmSRT_R). *)
Definition cmSRT (mc : word -> option byte) : Prop := forall P : Z -> Prop, shadow_rw_on P m -> shadow_rw_on P mc.

Lemma cmSRT_refl : cmSRT m.
Proof. intros P H. exact H. Qed.

Lemma cmSRT_R : forall mc, cmSRT mc -> shadow_rw_on cmR mc.
Proof. intros mc H. exact (H _ SRo). Qed.

(* A callee's forall-P post carries the transport across the call. *)
Lemma cmSRT_step : forall mc mc', cmSRT mc -> (forall P, shadow_rw_on P mc -> shadow_rw_on P mc') -> cmSRT mc'.
Proof. intros mc mc' H1 H2 P HP. exact (H2 P (H1 P HP)). Qed.

(* The frame's 32 shadow bytes are in R, on either arm (cmOn_R_fr; its cmOn_fr_facts is cmFK with CA unfolded). *)
Lemma cm_fr_R : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> forall k, 0 <= k < 32 -> cmR (shadow_addr fr + k).
Proof. intros fr sp2 jj nn FK k Hk. apply (cmOn_R_fr f len Sp FS fr sp2 jj nn FK). lia. Qed.

(* A shadow byte of the frame is writable and readable at a memory that carries the transport. *)
Lemma cm_srw_fr : forall fr sp2 jj nn mc a, cmFK fr sp2 jj nn -> cmSRT mc ->
  shadow_addr fr <= a < shadow_addr fr + 32 -> in_shadow a ->
  wview rsegs mc (wa a) <> None /\ exists b, mrd rsegs mc (wa a) = Some b.
Proof.
  intros fr sp2 jj nn mc a FK HS Ha Hs. exact (cmSRT_R mc HS a (cmOn_R_fr f len Sp FS fr sp2 jj nn FK a Ha) Hs).
Qed.

(* Each frame is 32-aligned, below the window top, writable and application memory, with writable shadow bytes. *)
Lemma fk_facts : forall fr sp2 jj nn, cmFK fr sp2 jj nn ->
  fr mod 32 = 0 /\ 0 < fr /\ fr + 192 <= CA /\
  (forall i, 0 <= i < 192 -> wview rsegs m (wa (fr + i)) <> None) /\
  (forall i, 0 <= i < 192 -> app_mem (fr + i)) /\
  (forall i, 0 <= i < 24 -> wview rsegs m (wa (shadow_addr fr + i)) <> None) /\
  (sp2 = CA \/ sp2 = CA - 192).
Proof.
  intros fr sp2 jj nn HFK.
  pose proof CA_facts as (CAm & CAlo & CAhi).
  destruct FP0 as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & P5) & _ & _ & _ & HFS & _).
  unfold FS_SIZE in HFS, P4. pose proof P5 as (_ & _ & P5h). unfold FS_SIZE in P5h.
  pose proof ST as (_ & _ & STh). destruct AW as (_ & _ & _ & AWh).
  assert (BASE : fr mod 32 = 0 /\ 0 < fr /\ fr + 192 <= CA /\
    (forall i, 0 <= i < 192 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 192 -> app_mem (fr + i)) /\ (sp2 = CA \/ sp2 = CA - 192)).
  { destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; subst fr sp2.
    - split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      split; [intros i Hi; apply (proj1 (STh (CA - 192 + i) ltac:(lia)))|].
      split; [|right; reflexivity].
      intros i Hi. replace (CA - 192 + i) with (Sp - 9136 + (CA - 192 + i - (Sp - 9136))) by lia.
      exact (proj1 (AWh (CA - 192 + i - (Sp - 9136)) ltac:(lia))).
    - assert (M32 : fs_frame FS 2 jj mod 32 = 0).
      { unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. Z.div_mod_to_equations; lia. }
      assert (LO : FS + 36864 <= fs_frame FS 2 jj).
      { unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
      assert (HI : fs_frame FS 2 jj + 256 <= FS + FS_SIZE).
      { unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
        change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj.
        unfold FS_SIZE. lia. }
      unfold FS_SIZE in HI.
      split; [exact M32|]. split; [lia|]. split; [lia|].
      split; [intros i Hi; exact (proj1 (P5h (fs_frame FS 2 jj + i) ltac:(lia)))|].
      split; [|left; reflexivity].
      intros i Hi. apply P4. lia. }
  destruct BASE as (B1 & B2 & B3 & B4 & B5 & B6).
  split; [exact B1|]. split; [exact B2|]. split; [exact B3|]. split; [exact B4|]. split; [exact B5|].
  split; [|exact B6].
  intros i Hi. pose proof (B5 (8 * i) ltac:(lia)) as Ap.
  pose proof (rt_app_shadow (fr + 8 * i) Ap) as Sh.
  rewrite <- (cm_sh_add8 fr i) by (clear -B1; Z.div_mod_to_equations; lia).
  refine (proj1 (SRo _ (cmOn_R_fr f len Sp FS fr sp2 jj nn HFK _ _) Sh)).
  rewrite (cm_sh_add8 fr i) by (clear -B1; Z.div_mod_to_equations; lia). lia.
Qed.

Lemma wtm_cases' : forall bs m (a x : word), write_to_mem m a bs x = m x \/ exists v, write_to_mem m a bs x = Some v.
Proof.
  induction bs as [|b bs IH]; intros m0 a x; cbn [write_to_mem]; [left; reflexivity|].
  destruct (IH (fun y => if bv_eqb y a then Some b else m0 y) (a + 1)%bv x) as [E|E]; [|right; exact E].
  rewrite E. destruct (bv_eqb x a); [right; eexists; reflexivity | left; reflexivity].
Qed.

(* ============================ generic memory facts ============================ *)

Lemma cm_stk_wv : forall mc lo hi a, stk rsegs mc lo hi -> lo <= a < hi -> wview rsegs mc (wa a) <> None.
Proof. intros mc lo hi a (_ & _ & H) Ha. exact (proj1 (H a Ha)). Qed.

Lemma cm_stk_rd : forall mc lo hi a, stk rsegs mc lo hi -> lo <= a < hi -> exists b, mrd rsegs mc (wa a) = Some b.
Proof. intros mc lo hi a (_ & _ & H) Ha. exact (proj2 (H a Ha)). Qed.

Lemma wv_store_ok : forall m0 mc a (n : nat),
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs m0 (wa (a + i)) <> None) -> wmono rsegs m0 mc ->
  0 <= a -> a + Z.of_nat n <= 2^64 -> store_ok rsegs mc (wa a) n = true.
Proof.
  intros m0 mc a n H Hw Ha Hn.
  assert (WR : wr_at rsegs mc a (Z.of_nat n)) by (split; [lia|]; split; [lia|]; intros i Hi; apply Hw, H, Hi).
  pose proof (wr_at_store_ok rsegs mc a (Z.of_nat n) 0 n WR ltac:(lia) ltac:(lia)) as HS.
  rewrite Z.add_0_r in HS. exact HS.
Qed.

(* n readable bytes at A are some byte list. *)
Lemma cm_rd_list : forall mc n A, 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> exists b, mrd rsegs mc (wa (A + i)) = Some b) ->
  exists bs, length bs = n /\ bytes_at rsegs mc A bs.
Proof.
  induction n as [|n IH]; intros A HA HN H.
  - exists []. split; [reflexivity|]. split; [lia|]. split; [cbn; lia|]. intros i Hi; cbn in Hi; lia.
  - destruct (H 0 ltac:(lia)) as [b0 E0]. rewrite Z.add_0_r in E0.
    destruct (IH (A + 1) ltac:(lia) ltac:(lia)) as (bs & Hl & (_ & _ & HB)).
    { intros i Hi. replace (A + 1 + i) with (A + (1 + i)) by lia. apply H. lia. }
    exists (b0 :: bs). split; [cbn; rewrite Hl; reflexivity|]. split; [lia|]. split; [cbn; lia|].
    intros i Hi. destruct i as [|i]; cbn [nth_error].
    + rewrite Z.add_0_r. exact E0.
    + cbn in Hi. rewrite <- (HB i ltac:(lia)). f_equal. f_equal. lia.
Qed.

(* n writable and readable bytes at A: a CB cell. *)
Lemma cm_rw_of : forall mc A n, 0 <= A -> A + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> wview rsegs mc (wa (A + i)) <> None /\ exists b, mrd rsegs mc (wa (A + i)) = Some b) ->
  exists junk, rw_cells rsegs mc A [CB n junk].
Proof.
  intros mc A n HA HN H.
  destruct (cm_rd_list mc n A HA HN (fun i Hi => proj2 (H i Hi))) as (bs & Hl & HB).
  exists bs. apply (cm_rw_of_bytes rsegs mc A bs n HB Hl).
  split; [lia|]. split; [lia|]. intros i Hi. exact (proj1 (H i Hi)).
Qed.

Lemma cm_rw_stk : forall mc lo hi A n, stk rsegs mc lo hi -> lo <= A -> A + Z.of_nat n <= hi ->
  exists junk, rw_cells rsegs mc A [CB n junk].
Proof.
  intros mc lo hi A n Hs H1 H2. pose proof Hs as (H0 & Hh & _).
  apply cm_rw_of; [lia | lia |]. intros i Hi. pose proof Hs as (_ & _ & H). apply H. lia.
Qed.

Lemma cm_shadow_rw_write : forall mc a bs, cmSRT mc -> cmSRT (write_to_mem mc a bs).
Proof.
  intros mc a bs H P HP x Px Hx. destruct (H P HP x Px Hx) as [Hw (b & Hb)]. split; [apply wview_write_mono, Hw|].
  unfold mrd in *. destruct (wtm_cases' bs mc a (wa x)) as [E|[v E]]; rewrite E; [exists b; exact Hb | exists v; reflexivity].
Qed.

(* ============================ the invariant ============================ *)

Hypothesis BT : bytes_at rsegs m CM_T CM_TBL.

(* The 13 callee-saved registers stored at [Sp - 104, Sp): s11 .. ra ascending. *)
Definition cmSAVES : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* The window's bytes outside the frame are addressable. *)
Definition AWX (fr : Z) (mc : word -> option byte) : Prop :=
  forall x, Sp - 9136 <= x < Sp -> ~ (fr <= x < fr + 192) -> addr_byte mc x.

(* The cells the bcmp wrapper reads. *)
Definition aCL (mc : word -> option byte) : Prop :=
  bytes_at rsegs mc REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mc REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs mc GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mc (CF + 254) [Z_to_bv 8 1] /\
  bytes_at rsegs mc (CF + 255) [Z_to_bv 8 1].

(* The bytes outside the window and the side stack that the run reads. *)
Definition EXT (mc : word -> option byte) : Prop :=
  (50 <= len -> bytes_at rsegs mc f fb /\ addressable mc f 50) /\
  addressable mc CM_T 3256 /\ bytes_at rsegs mc CM_T CM_TBL /\ addressable mc REAC_CTRL_PARSE_BC 6 /\ aCL mc.

(* The runtime state. *)
Definition RT (mc : word -> option byte) : Prop :=
  asan_cells mc /\ cmSRT mc /\ fp [0%nat; 1%nat; 2%nat] mc (bv_unsigned tp) FS (Sp - 9136) Sp aWf aDf /\ aTL mc.

(* The state carried through the body: the frame geometry, the writes, the runtime state, the window addressable
   outside the frame, the bytes outside, the window and the frame readable and writable, the saves, and (side-stack
   frame) the flag address the release reads. *)
Definition cmJ (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  cmFK fr sp2 jj nn /\ munch aWc m mc /\ wmono rsegs m mc /\ mem_inv rsegs mc /\ RT mc /\ AWX fr mc /\ EXT mc /\
  stk rsegs mc (Sp - 9136) Sp /\ stk rsegs mc fr (fr + 192) /\ rw_cells rsegs mc (Sp + -104) cmSAVES /\
  (nn = 1 -> bytes_at rsegs mc (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj)))).

Definition cmPost : machine_state -> Prop := fun ms' =>
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom rsegs) /\
    munch ([(Sp - 9136, Sp)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (Sp - 9136), shadow_addr Sp)]) m m' /\
    wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' (Sp - 9136) Sp /\
    asan_cells m' /\ (forall P, shadow_rw_on P m -> shadow_rw_on P m') /\ addressable m' (Sp - 9136) 9136 /\
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
      (reac_box_catalogue_match_D f len) /\
    reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (Sp - 9136) Sp.

Lemma nth_fold1 : forall (wl : list byte) ks q bs,
  length wl = 1%nat -> (q < length bs)%nat -> (forall k, In k ks -> (k < length bs)%nat) ->
  nth_error (fold_left (fun l k => upd_bytes l k wl) ks bs) q =
    (if in_dec Nat.eq_dec q ks then nth_error wl 0 else nth_error bs q).
Proof.
  intros wl ks. induction ks as [|k ks IH]; intros q bs Hw Hq Hk; cbn [fold_left].
  - reflexivity.
  - assert (Hkb : (k < length bs)%nat) by (apply Hk; left; reflexivity).
    assert (Hlen : length (upd_bytes bs k wl) = length bs) by (apply upd_bytes_length; lia).
    rewrite (IH q (upd_bytes bs k wl) Hw ltac:(rewrite Hlen; exact Hq)
               ltac:(intros k0 Hk0; rewrite Hlen; apply Hk; right; exact Hk0)).
    rewrite (upd_bytes_nth bs k wl q ltac:(lia) Hq).
    cbn [In].
    destruct (in_dec Nat.eq_dec q ks) as [Hin|Hnin].
    + destruct (in_dec Nat.eq_dec q (k :: ks)) as [_|Hnin']; [reflexivity|].
      exfalso; apply Hnin'; right; exact Hin.
    + destruct ((k <=? q)%nat && (q <? k + length wl)%nat)%bool eqn:Econd.
      * apply andb_true_iff in Econd. destruct Econd as [HA HB].
        apply Nat.leb_le in HA. apply Nat.ltb_lt in HB. rewrite Hw in HB.
        assert (Eqk : q = k) by lia. subst q. rewrite Nat.sub_diag.
        destruct (in_dec Nat.eq_dec k (k :: ks)) as [_|Hnin']; [reflexivity|].
        exfalso; apply Hnin'; left; reflexivity.
      * destruct (in_dec Nat.eq_dec q (k :: ks)) as [Hin'|_]; [|reflexivity].
        exfalso. destruct Hin' as [E|E]; [| contradiction].
        subst q. rewrite Nat.leb_refl in Econd. rewrite Hw in Econd. cbn [andb] in Econd.
        apply Nat.ltb_ge in Econd. lia.
Qed.

Lemma cm_sh_sok : forall mc a, cmSRT mc -> cmR a -> in_shadow a -> store_ok rsegs mc (wa a) 1 = true.
Proof.
  intros mc a HS HR Ha. pose proof (rt_shadow_bound a Ha) as R.
  apply (wv_store_ok mc mc a 1);
    [ intros i Hi; replace (a + i) with a by lia; exact (proj1 (cmSRT_R mc HS a HR Ha)) | apply wmono_refl | lia | lia ].
Qed.

Lemma cm_sh_div : forall fr d, fr mod 8 = 0 -> shadow_addr (fr + d) = shadow_addr fr + d / 8.
Proof. intros fr d Hf. unfold shadow_addr. Z.div_mod_to_equations. lia. Qed.

Lemma addr_byte_keep : forall W mm mm2 x, addr_byte mm x -> munch W mm mm2 ->
  outside W (shadow_addr x) -> addr_byte mm2 x.
Proof.
  intros W mm mm2 x (Hap & b & Hmrd & Hok) MU Ho. split; [exact Hap|]. exists b. split; [|exact Hok].
  pose proof (rt_shadow_bound (shadow_addr x) (rt_app_shadow x Hap)) as R.
  assert (E : mm2 (wa (shadow_addr x)) = mm (wa (shadow_addr x)))
    by (apply MU; rewrite wa_unsigned by lia; exact Ho).
  unfold mrd in *. rewrite E. exact Hmrd.
Qed.

Ltac tcell DJ sel :=
  eapply fl_bytes; [eassumption | eassumption |
    let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
    rewrite ?length_app, ?length_le8, ?length_le4, ?length_le1 in Hx; cbn [length] in Hx;
    eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; sel; reflexivity | lia] ].

Lemma fl_tls_cells : forall mm mm2 W TP DT TS C T DB k,
  asan_tls_cells mm TP DT TS C T DB k -> munch W mm mm2 ->
  fp_dj W (fp_tls TP DT TS C T DB k) ->
  asan_tls_cells mm2 TP DT TS C T DB k.
Proof.
  intros mm mm2 W TP DT TS C T DB k HT Hm DJ.
  unfold asan_tls_cells in HT |- *.
  destruct HT as (c1 & c2 & c3 & c4 & c5 & c6k & c7 & c8 & c9 & c10 & c11ex & c12 & c13 & c14 & c15 & c16 & c17 & c18db & c19).
  split; [tcell DJ ltac:(left)|]. split; [tcell DJ ltac:(do 1 right; left)|].
  split; [tcell DJ ltac:(do 2 right; left)|]. split; [tcell DJ ltac:(do 3 right; left)|].
  split; [tcell DJ ltac:(do 4 right; left)|]. split; [exact c6k|].
  split; [tcell DJ ltac:(do 5 right; left)|]. split; [tcell DJ ltac:(do 6 right; left)|].
  split; [tcell DJ ltac:(do 7 right; left)|]. split; [tcell DJ ltac:(do 8 right; left)|].
  split; [destruct c11ex as (tb & te & c11); exists tb, te; tcell DJ ltac:(do 9 right; left)|].
  split; [tcell DJ ltac:(do 10 right; left)|]. split; [tcell DJ ltac:(do 11 right; left)|].
  split; [tcell DJ ltac:(do 12 right; left)|]. split; [tcell DJ ltac:(do 13 right; left)|].
  split; [tcell DJ ltac:(do 14 right; left)|]. split; [tcell DJ ltac:(do 2 right; left)|].
  split; [exact c18db|]. tcell DJ ltac:(do 15 right; left).
Qed.

Definition cm_ks : list nat := [4;5;6;7;0;1;2;3;12;13;14;15;8;9;10;11;20;21;22;23;16;17;18;19]%nat.
Lemma cm_ks_bound : forall k, In k cm_ks -> (k < 24)%nat.
Proof. intros k Hk; unfold cm_ks in Hk; cbn [In] in Hk; decompose [or] Hk; subst; lia. Qed.
Lemma cm_ks_cover : forall q, (q < 24)%nat -> In q cm_ks.
Proof.
  intros q Hq; unfold cm_ks.
  do 24 (destruct q as [|q]; [cbn [In]; repeat (first [left; reflexivity | right])|]). lia.
Qed.

Ltac shst fr0 mc0 k :=
  lazymatch goal with
  | [ SHIN : forall kk, _ -> in_shadow (shadow_addr fr0 + kk),
      FRR : forall kk, _ -> cmR (shadow_addr fr0 + kk),
      WMc : wmono rsegs mc0 ?mcur,
      SRcur : cmSRT ?mcur,
      Jmicur : mem_inv rsegs ?mcur,
      MUc : munch ?W mc0 ?mcur,
      BSH : bytes_at rsegs ?mcur (shadow_addr fr0) ?cs,
      STwcur : stk rsegs ?mcur (Sp - 9136) Sp,
      Lcs : length ?cs = 24%nat
      |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) ] =>
    let SOK := fresh "SOK" in
    assert (SOK : store_ok rsegs mcur (wa (shadow_addr fr0 + k)) 1 = true)
      by (apply cm_sh_sok; [exact SRcur | apply FRR; lia | apply SHIN; lia]);
    step;
    apply (wmono_write rsegs mc0 mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in WMc;
    apply (cm_shadow_rw_write mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in SRcur;
    apply (mem_inv_store rsegs mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 0))) in Jmicur;
      [| rewrite length_le1; exact SOK];
    apply (stk_write rsegs mcur (Sp - 9136) Sp (shadow_addr fr0 + k) (le1 (Z_to_bv 64 0))) in STwcur;
      [| lia | rewrite length_le1; lia];
    apply (munch_write W mc0 mcur (shadow_addr fr0 + k) (le1 (Z_to_bv 64 0))) in MUc;
      [| lia | rewrite length_le1; lia | rewrite length_le1; cbn [inside]; right; left; split; lia];
    let B2 := fresh "BSHn" in
    pose proof (bytes_at_write_inside rsegs mcur (shadow_addr fr0) cs k (le1 (Z_to_bv 64 0)) BSH ltac:(lia)
                 ltac:(rewrite length_le1, Lcs; lia)) as B2;
    let L2 := fresh "Lcsn" in
    assert (L2 : length (upd_bytes cs (Z.to_nat k) (le1 (Z_to_bv 64 0))) = 24%nat)
      by (rewrite upd_bytes_length; [exact Lcs | rewrite length_le1, Lcs; lia]);
    clear BSH Lcs SOK; rename B2 into BSH; rename L2 into Lcs
  end.

Ltac shstf fr0 mc0 k :=
  lazymatch goal with
  | [ SHIN : forall kk, _ -> in_shadow (shadow_addr fr0 + kk),
      FRR : forall kk, _ -> cmR (shadow_addr fr0 + kk),
      WMc : wmono rsegs mc0 ?mcur,
      SRcur : cmSRT ?mcur,
      Jmicur : mem_inv rsegs ?mcur,
      MUc : munch ?W mc0 ?mcur,
      STwcur : stk rsegs ?mcur (Sp - 9136) Sp
      |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) ] =>
    let SOK := fresh "SOK" in
    assert (SOK : store_ok rsegs mcur (wa (shadow_addr fr0 + k)) 1 = true)
      by (apply cm_sh_sok; [exact SRcur | apply FRR; lia | apply SHIN; lia]);
    step;
    apply (wmono_write rsegs mc0 mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in WMc;
    apply (cm_shadow_rw_write mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in SRcur;
    apply (mem_inv_store rsegs mcur (wa (shadow_addr fr0 + k)) (le1 (Z_to_bv 64 (-11)))) in Jmicur;
      [| rewrite length_le1; exact SOK];
    apply (stk_write rsegs mcur (Sp - 9136) Sp (shadow_addr fr0 + k) (le1 (Z_to_bv 64 (-11)))) in STwcur;
      [| lia | rewrite length_le1; lia];
    apply (munch_write W mc0 mcur (shadow_addr fr0 + k) (le1 (Z_to_bv 64 (-11)))) in MUc;
      [| lia | rewrite length_le1; lia | rewrite length_le1; cbn [inside]; right; left; split; lia];
    clear SOK
  end.

(* ============================ the footprint facts ============================ *)

Lemma rf_fpw : forall iv, In iv (fp_w [0%nat; 1%nat; 2%nat] FS) -> rng RNG (fst iv) (snd iv - fst iv).
Proof. intros iv Hiv. exact (proj1 (Forall_forall _ _) RFPW iv Hiv). Qed.

(* The class-c side-stack bytes, as a callee's text (fp_w [c] FS) names them. *)
Lemma rf_fpw_c : forall c, In c [0%nat; 1%nat; 2%nat] ->
  Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [c] FS).
Proof. intros c Hc. apply Forall_forall. intros iv Hiv. apply rf_fpw. exact (fp_w_incl c _ FS Hc iv Hiv). Qed.

(* The class-c frame area and its shadow, as __asan_stack_malloc_c's text names them. *)
Lemma rf_area : forall c, In c [0%nat; 1%nat; 2%nat] ->
  rng RNG (fs_frame FS c 0) (2 ^ 20) /\ rng RNG (shadow_addr (fs_frame FS c 0)) (fs_shadow_area c).
Proof.
  intros c Hc.
  assert (Hc2 : (c <= 2)%nat) by (destruct Hc as [<-|[<-|[<-|[]]]]; lia).
  destruct (fs_frame_span FS c Hc2) as (E1 & E2 & E3).
  destruct acl_fs as (FSpos & FSmod & _ & _ & _ & _).
  pose proof (rf_fpw _ (fpw3_in_frame FS c Hc)) as R1. pose proof (rf_fpw _ (fpw3_in_shadow FS c Hc)) as R2.
  cbn [fst snd] in R1, R2. rewrite E1 in R1, R2. rewrite E2.
  assert (M8 : fs_frame FS c 0 mod 8 = 0) by (rewrite E3; Z.div_mod_to_equations; lia).
  set (b := fs_frame FS c 0) in *. clearbody b. change (2 ^ 20) with 1048576.
  split; [apply (rng_sub RNG _ _ _ _ R1); lia |].
  apply (rng_sub RNG _ _ _ _ R2); [lia |]. unfold shadow_addr. Z.div_mod_to_equations; lia.
Qed.

(* The class-2 flag byte j is in the side stack's header. *)
Lemma rf_flag2 : forall j, 0 <= j < fs_M 2 -> rng RNG (fs_flag FS 2 j) 1.
Proof.
  intros j Hj. change (fs_M 2) with 4096 in Hj.
  assert (E0 : fs_frame FS 0 0 = FS + 36864) by (unfold fs_frame; change (Z.of_nat 0) with 0; lia).
  assert (EF : fs_flag FS 2 j = FS + 28672 + j)
    by (unfold fs_flag; change (2 ^ (15 - Z.of_nat 2)) with 8192; change (2 ^ 15) with 32768; lia).
  apply (rng_sub RNG _ _ _ _ RHDR); rewrite ?E0, ?EF; lia.
Qed.

(* The class-2 ASan frame (a real-stack frame CA - 192 in the window, or a side-stack frame fs_frame FS 2 jj), its
   256 bytes, its 32 shadow bytes and the shadow word cover of each of its parts. *)
Lemma cm_fr_rng : forall fr sp2 jj nn, cmFK fr sp2 jj nn ->
  rng RNG fr 256 /\ rng RNG (shadow_addr fr) 32 /\
  (forall p n, fr <= p -> 0 < n -> p + n <= fr + 256 -> sh_cover RNG p n).
Proof.
  intros fr sp2 jj nn FK.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  pose proof S16 as S16'.
  destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)].
  - subst fr.
    split; [apply (rng_sub RNG _ _ _ _ RWIN); lia|].
    split.
    + apply (rng_sub RNG _ _ _ _ RWSH); unfold shadow_addr; Z.div_mod_to_equations; lia.
    + intros p n H1 H2 H3. apply (shc_in RNG _ _ p n RWSH); unfold shadow_addr; Z.div_mod_to_equations; lia.
  - destruct acl_fs as (FSpos & FSmod & _ & _ & _ & _).
    pose proof (rf_fpw _ (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as R1.
    pose proof (rf_fpw _ (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as R2. cbn [fst snd] in R1, R2.
    destruct (fs_frame_span FS 2 ltac:(lia)) as (E1 & _ & E3).
    rewrite E1 in R1, R2.
    assert (Efr : fs_frame FS 2 jj = fs_frame FS 2 0 + jj * 256)
      by (unfold fs_frame; change (fs_B 2) with 256; lia).
    change (fs_M 2) with 4096 in Hj.
    assert (M64 : fs_frame FS 2 0 mod 64 = 0)
      by (rewrite E3; cbn [Z.of_nat Pos.of_succ_nat]; Z.div_mod_to_equations; lia).
    subst fr. rewrite Efr. set (b := fs_frame FS 2 0) in *. clearbody b. clear E1 E3 Efr.
    split; [apply (rng_sub RNG _ _ _ _ R1); lia|].
    split; [apply (rng_sub RNG _ _ _ _ R2); unfold shadow_addr; Z.div_mod_to_equations; lia|].
    intros p n H1 H2 H3. apply (shc_in RNG _ _ p n R2); unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia.
Qed.

(* A callee's window [lo, hi) inside the window, and its byte-exact shadow. *)
Lemma cm_win_rng : forall lo hi, Sp - 9136 <= lo -> lo <= hi -> hi <= Sp ->
  rng RNG lo (hi - lo) /\ rng RNG (shadow_addr lo) (shadow_addr hi - shadow_addr lo).
Proof.
  intros lo hi H1 H2 H3. split; [apply (rng_sub RNG _ _ _ _ RWIN); lia|].
  pose proof (acl_sh_ge lo (Sp - 9136) H1). pose proof (acl_sh_ge Sp hi H3). pose proof (acl_sh_ge hi lo H2).
  apply (rng_sub RNG _ _ _ _ RWSH); lia.
Qed.

(* The shadow word cover of a range 64 bytes inside the window. *)
Lemma cm_win_shc : forall p n, Sp - 9136 + 64 <= p -> 0 < n -> p + n + 64 <= Sp -> sh_cover RNG p n.
Proof.
  intros p n H1 H2 H3. pose proof S16 as S16'.
  apply (shc_in RNG _ _ p n RWSH); unfold shadow_addr; Z.div_mod_to_equations; lia.
Qed.

(* The thread cells at a memory reached from m by writes inside aWc are those of m (asan_tls_cells pins them). *)
Lemma cm_tls_back : forall mc W, munch W m mc -> sub_fp W aWc ->
  forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
    asan_tls_cells m (bv_unsigned tp) DT TS C T DB kk.
Proof.
  intros mc W MU SUB DT TS C T DB kk HT.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd0 & _).
  assert (apart : Forall (fun d => forall x, fst d <= x < snd d -> outside W x)
                    (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
  { apply Forall_forall. intros [a b] Hin x Hx. apply SUB. unfold aWc. cbn [outside]. split.
    - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                    HWd0 (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
      unfold aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
    - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
               (TLS0 DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
  destruct (fl_tls_same m mc W (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HT MU apart)
    as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
  exact HT0.
Qed.

Lemma cm_tls_rng : forall mc W, munch W m mc -> sub_fp W aWc ->
  forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB kk).
Proof.
  intros mc W MU SUB DT TS C T DB kk HT. exact (RTLS DT TS C T DB kk (cm_tls_back mc W MU SUB DT TS C T DB kk HT)).
Qed.

(* ============================ the side-stack release ============================ *)

(* A range [a, b) inside a range of X: every range of T that is apart from X is apart from [a, b). *)
Lemma cm_dj_in : forall T X a' b' a b, fp_dj T X -> In (a', b') X -> a' <= a -> b <= b' ->
  Forall (fun d => ly_dj a b (fst d) (snd d)) T.
Proof.
  intros T X a' b' a b H Hin H1 H2. unfold fp_dj in H. eapply Forall_impl; [|exact H].
  intros [c d] Hd. cbn beta in Hd. rewrite Forall_forall in Hd. pose proof (Hd _ Hin) as D.
  unfold ly_dj in *. cbn [fst snd] in *. lia.
Qed.

(* A byte list at A after a run that kept every byte of it except the byte at A + j, which now reads b0. *)
Lemma cm_bytes_upd1 : forall W' mm mm2 A bs j b0,
  bytes_at rsegs mm A bs -> munch W' mm mm2 -> 0 <= j < Z.of_nat (length bs) ->
  (forall x, A <= x < A + Z.of_nat (length bs) -> x <> A + j -> outside W' x) ->
  mrd rsegs mm2 (wa (A + j)) = Some b0 ->
  bytes_at rsegs mm2 A (upd_bytes bs (Z.to_nat j) [b0]).
Proof.
  intros W' mm mm2 A bs j b0 (H0 & Hl & HB) Hm Hj HO Hrd.
  assert (L : length (upd_bytes bs (Z.to_nat j) [b0]) = length bs)
    by (apply upd_bytes_length; cbn [length]; lia).
  split; [exact H0|]. split; [rewrite L; exact Hl|].
  intros i Hi. rewrite L in Hi.
  rewrite (upd_bytes_nth bs (Z.to_nat j) [b0] i ltac:(cbn [length]; lia) Hi).
  destruct (Nat.eq_dec i (Z.to_nat j)) as [Ei|Ne].
  - subst i.
    match goal with |- context [if ?c then _ else _] =>
      replace c with true by (symmetry; apply andb_true_iff; split; [apply Nat.leb_le | apply Nat.ltb_lt];
                              cbn [length]; lia) end.
    rewrite Nat.sub_diag. cbn [nth_error]. rewrite Z2Nat.id by lia. exact Hrd.
  - assert (KEEP : mrd rsegs mm2 (wa (A + Z.of_nat i)) = nth_error bs i).
    { rewrite <- (HB i Hi). unfold mrd. rewrite Hm; [reflexivity|]. rewrite wa_unsigned by lia. apply HO; lia. }
    rewrite KEEP.
    match goal with |- context [if ?c then _ else _] => destruct c eqn:E; [|reflexivity] end.
    apply andb_true_iff in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2. cbn [length] in E2.
    exfalso; lia.
Qed.

Lemma cm_forall_firstn : forall (P : byte -> Prop) n l, Forall P l -> Forall P (firstn n l).
Proof.
  intros P n. induction n as [|n IH]; intros l H; [cbn [firstn]; constructor|].
  destruct H as [|x l0 Hx Hl]; cbn [firstn]; [constructor | constructor; [exact Hx | apply IH; exact Hl]].
Qed.

Lemma cm_forall_skipn : forall (P : byte -> Prop) n l, Forall P l -> Forall P (skipn n l).
Proof.
  intros P n. induction n as [|n IH]; intros l H; [exact H|].
  destruct H as [|x l0 Hx Hl]; cbn [skipn]; [constructor | apply IH; exact Hl].
Qed.

Lemma cm_forall_upd : forall (P : byte -> Prop) bs k ws, Forall P bs -> Forall P ws -> Forall P (upd_bytes bs k ws).
Proof.
  intros P bs k ws H Hw. unfold upd_bytes. apply Forall_app. split; [apply cm_forall_firstn; exact H|].
  apply Forall_app. split; [exact Hw | apply cm_forall_skipn; exact H].
Qed.

(* The class-0 and class-1 state lies in [FS, FS + 28672): it survives writes apart from the side stack's first
   36864 bytes except one byte fl at or above FS + 28672. *)
Lemma cm_cls_keep : forall W' mm mm2 c fl, (c <= 1)%nat -> FS + 28672 <= fl ->
  (forall x, FS <= x < FS + 36864 -> x <> fl -> outside W' x) -> munch W' mm mm2 ->
  fp_cls mm FS c -> fp_cls mm2 FS c.
Proof.
  intros W' mm mm2 c fl Hc Hfl BEL Hm (Hc6 & h & flags & HH & HFg & HFl & HFb).
  assert (B : FS <= fs_hint FS c /\ fs_hint FS c + 8 <= FS + 28672 /\
              FS <= fs_flag FS c 0 /\ fs_flag FS c 0 + fs_M c <= FS + 28672).
  { unfold fs_hint, fs_flag, fs_M. destruct c as [|[|c]]; [simpl; lia | simpl; lia | exfalso; lia]. }
  split; [exact Hc6|]. exists h, flags.
  split; [eapply fl_bytes; [exact HH | exact Hm | intros x Hx; rewrite length_le8 in Hx; apply BEL; lia]|].
  split; [eapply fl_bytes; [exact HFg | exact Hm | intros x Hx; apply BEL; lia]|].
  split; assumption.
Qed.

(* The class-2 state after the release of frame j: the flag byte j reads 0, every other byte of the class-2 state is
   kept. *)
Lemma cm_cls_rel : forall W' mm mm2 j, 0 <= j < fs_M 2 ->
  (forall x, FS <= x < FS + 36864 -> x <> fs_flag FS 2 j -> outside W' x) -> munch W' mm mm2 ->
  mrd rsegs mm2 (wa (fs_flag FS 2 j)) = Some (Z_to_bv 8 0) -> fp_cls mm FS 2 -> fp_cls mm2 FS 2.
Proof.
  intros W' mm mm2 j Hj BEL Hm Hrd (Hc6 & h & flags & HH & HFg & HFl & HFb).
  assert (E1 : fs_hint FS 2 = FS + 16) by (unfold fs_hint; cbn [Z.of_nat Pos.of_succ_nat]; lia).
  assert (E2 : fs_flag FS 2 j = fs_flag FS 2 0 + j) by (unfold fs_flag; lia).
  assert (E3 : fs_flag FS 2 0 = FS + 28672)
    by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 15) with 32768; change (2 ^ 13) with 8192; lia).
  assert (E4 : fs_M 2 = 4096) by reflexivity.
  split; [exact Hc6|]. exists h, (upd_bytes flags (Z.to_nat j) [Z_to_bv 8 0]).
  split; [eapply fl_bytes; [exact HH | exact Hm | intros x Hx; rewrite length_le8 in Hx; apply BEL; lia]|].
  split; [|split].
  - apply (cm_bytes_upd1 W' mm mm2 (fs_flag FS 2 0) flags j (Z_to_bv 8 0) HFg Hm); [lia | | rewrite <- E2; exact Hrd].
    intros x Hx Hne. apply BEL; lia.
  - rewrite upd_bytes_length; [exact HFl | cbn [length]; lia].
  - apply cm_forall_upd; [exact HFb | constructor; [left; reflexivity | constructor]].
Qed.

(* The side-stack exit (nn = 1) at the release store 0x85194 (sb zero, 0(a0), a0 = fs_flag FS 2 jj): the invariant
   at the exit memory mc; the exit's writes so far (the frame's first word, its 32 shadow bytes) inside
   [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]; mem_inv, the
   writable shadow, the window and the side stack readable and writable at the store memory m1. *)
Definition cmAtRel (fr sp2 jj : Z) (mc m1 : word -> option byte) : Prop :=
  cmJ fr sp2 jj 1 mc /\
  munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc m1 /\
  wmono rsegs mc m1 /\ mem_inv rsegs m1 /\ cmSRT m1 /\ stk rsegs m1 (Sp - 9136) Sp /\
  stk rsegs m1 FS (FS + FS_SIZE).

(* The side-stack exit (nn = 1) from 0x850fc to the release store at 0x85194: the frame's first word := the retired
   magic, the frame's 32 shadow bytes := 0xf5, a0 := the flag word at fr + 248. *)
Lemma cm_pre_rel : forall fr sp2 jj mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmJ fr sp2 jj 1 mc ->
  evtF rsegs RNG
    (fun ms => exists m1, ms =
       MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
               (Z_to_bv 64 (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
               (Z_to_bv 64 fr) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               z9 z10 z11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x85194) fc None m1 (seg_rom rsegs) /\ cmAtRel fr sp2 jj mc m1)
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if 1 =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850fc) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HJ.
  pose proof HJ as HJk.
  destruct HJ as (HFK & Jmu & Jwm & Jmi & JRT & JAWX & JEXT & STw & STf & SAV & FLG).
  destruct JRT as (JAC & JSR & JFP & JTL).
  pose proof (fk_facts fr sp2 jj 1 HFK) as (Fm32 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof (cm_fr_R fr sp2 jj 1 HFK) as FRR.
  pose proof (cm_fr_rng fr sp2 jj 1 HFK) as (RFR & RFS & _).
  pose proof CA_facts as (CAm & CAlo & CAhi).
  assert (Fm8 : fr mod 8 = 0) by (clear -Fm32; Z.div_mod_to_equations; lia).
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - discriminate En.
  - clear En.
    destruct acl_fs as (AF1 & AF2 & AF3 & AF4 & AF5 & AF6).
    assert (FRlo : FS + 36864 <= fr).
    { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
    assert (FRhi : fr + 256 <= FS + FS_SIZE).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj.
      unfold FS_SIZE in *. lia. }
    assert (SOKfr : store_ok rsegs mc (wa fr) 8 = true) by
      (apply (wv_store_ok mc mc fr 8);
        [ intros i Hi; apply (cm_stk_wv mc fr (fr + 192) (fr + i) STf); lia | apply wmono_refl | lia | lia ]).
    assert (SHIN : forall k, 0 <= k < 32 -> in_shadow (shadow_addr fr + k)).
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply AF5.
      unfold FS_SIZE in *. lia. }
    assert (SBlo : 0 <= shadow_addr fr) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
    assert (SBhi : shadow_addr fr + 40 <= 2 ^ 64) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 31) (SHIN 31 ltac:(lia))); lia).
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof JSR as SRcur.
    pose proof Jmi as Jmicur.
    pose proof (munch_refl [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                            (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mc) as MUc.
    pose proof STw as STwcur.
    step. step. step.
    change (Z_to_bv 64 fr) with (wa fr).
    apply (wmono_write rsegs mc mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in WMc.
    apply (cm_shadow_rw_write mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in SRcur.
    apply (mem_inv_store rsegs mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in Jmicur;
      [| rewrite length_le8; exact SOKfr].
    apply (munch_write _ mc mc fr (le8 (Z_to_bv 64 1172321806))) in MUc;
      [| lia | rewrite length_le8; lia | cbn [inside]; left; split; [lia | rewrite length_le8; lia]].
    apply (stk_write rsegs mc (Sp - 9136) Sp fr (le8 (Z_to_bv 64 1172321806))) in STwcur;
      [| lia | rewrite length_le8; lia].
    replace (if (1 =? 0)%Z then 0 else fr) with fr by reflexivity.
    step. rewrite (cm_eqb0 fr) by lia.
    replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
    step.
    shstf fr mc 4. shstf fr mc 5. shstf fr mc 6. shstf fr mc 7. shstf fr mc 0. shstf fr mc 1. shstf fr mc 2. shstf fr mc 3.
    shstf fr mc 12. shstf fr mc 13. shstf fr mc 14. shstf fr mc 15. shstf fr mc 8. shstf fr mc 9. shstf fr mc 10. shstf fr mc 11.
    shstf fr mc 20. shstf fr mc 21. shstf fr mc 22. shstf fr mc 23. shstf fr mc 16. shstf fr mc 17. shstf fr mc 18. shstf fr mc 19.
    shstf fr mc 28. shstf fr mc 29. shstf fr mc 30. shstf fr mc 31. shstf fr mc 24. shstf fr mc 25. shstf fr mc 26. shstf fr mc 27.
    specialize (FLG eq_refl).
    pose proof (rf_flag2 jj Hj) as RFL.
    pose proof JFP as JFPc.
    destruct JFPc as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & HPfs & _ & _ & _ & _ & _ & _ & _).
    destruct HPfs as (FSP1 & FSP2 & FSP3 & FSP4 & FSPstk).
    assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
    assert (FLapp : forall d, 248 <= d < 256 -> app_mem (fr + d)) by
      (intros d Hd; apply AF5; unfold FS_SIZE in *; lia).
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      assert (FLGm : bytes_at rsegs m1 (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))))
        by (eapply fl_bytes; [exact FLG | exact MUc |
             intros x Hx; rewrite length_le8 in Hx; cbn [outside];
             split; [lia | split; [ intros [A B];
               apply (acl_app_not_shadow x);
               [ replace x with (fr + (x - fr)) by lia; apply FLapp; lia
               | pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HS;
                 replace (shadow_addr fr + (x - shadow_addr fr)) with x in HS by lia; exact HS ]
               | split; [ clear -Hx FLo FRlo; lia | exact I ]]]]);
      assert (RD : ov_read_bytes rsegs m1 (wa (fr + 248)) 8 = Some (le8 (Z_to_bv 64 (fs_flag FS 2 jj))))
        by (replace (fr + 248) with (fr + 248 + 0) by lia;
            rewrite (bytes_at_read rsegs m1 _ (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) 0 8 FLGm)
              by (try rewrite length_le8; lia); reflexivity);
      assert (SOKfl : store_ok rsegs m1 (wa (fs_flag FS 2 jj)) 1 = true)
        by (apply (wv_store_ok mc m1 (fs_flag FS 2 jj) 1);
            [ intros i Hi; replace (fs_flag FS 2 jj + i) with (fs_flag FS 2 jj) by lia;
              apply (cm_stk_wv mc FS (FS + FS_SIZE) (fs_flag FS 2 jj) FSPstk); unfold FS_SIZE in *; lia
            | exact WMc | lia | unfold FS_SIZE in *; lia ]);
      assert (STfs1 : stk rsegs m1 FS (FS + FS_SIZE))
        by (repeat (apply stk_write; [| lia | rewrite ?length_le1, ?length_le8; lia]); exact FSPstk) end.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
    step.
    apply evtF_done. cbv beta. exists m1. split; [reflexivity|].
    exact (conj HJk (conj MUc (conj WMc (conj Jmicur (conj SRcur (conj STwcur STfs1)))))).
Qed.

(* The side-stack exit after the release store (the flag byte fs_flag FS 2 jj := 0), from 0x85198 to the return:
   the epilogue restores the saves, and cmPost holds at the released memory. *)
Lemma cm_post_rel : forall fr sp2 jj mc m1 r
    (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmAtRel fr sp2 jj mc m1 ->
  evtF rsegs RNG cmPost
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             (Z_to_bv 64 (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
             z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x85198) fc None (write_to_mem m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0)))
        (seg_rom rsegs)).
Proof.
  intros fr sp2 jj mc m1 r x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HAt.
  destruct HAt as (HJ & MUc & WMc & Jmicur & SRcur & STwcur & STfs1).
  destruct HJ as (HFK & Jmu & Jwm & Jmi & JRT & JAWX & JEXT & STw & STf & SAV & FLG).
  destruct JRT as (JAC & JSR & JFP & JTL).
  pose proof (fk_facts fr sp2 jj 1 HFK) as (Fm32 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof (cm_fr_R fr sp2 jj 1 HFK) as FRR.
  pose proof (cm_fr_rng fr sp2 jj 1 HFK) as (RFR & RFS & _).
  pose proof CA_facts as (CAm & CAlo & CAhi).
  assert (Fm8 : fr mod 8 = 0) by (clear -Fm32; Z.div_mod_to_equations; lia).
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - discriminate En.
  - clear En.
    destruct acl_fs as (AF1 & AF2 & AF3 & AF4 & AF5 & AF6).
    assert (FRlo : FS + 36864 <= fr).
    { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. lia. }
    assert (FRhi : fr + 256 <= FS + FS_SIZE).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj.
      unfold FS_SIZE in *. lia. }
    assert (SHIN : forall k, 0 <= k < 32 -> in_shadow (shadow_addr fr + k)).
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply AF5.
      unfold FS_SIZE in *. lia. }
    assert (SBlo : 0 <= shadow_addr fr) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
    assert (SBhi : shadow_addr fr + 40 <= 2 ^ 64) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 31) (SHIN 31 ltac:(lia))); lia).
    specialize (FLG eq_refl).
    pose proof (rf_flag2 jj Hj) as RFL.
    pose proof JFP as JFPc.
    destruct JFPc as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & HPfs & _ & _ & _ & _ & _ & _ & _).
    destruct HPfs as (FSP1 & FSP2 & FSP3 & FSP4 & FSPstk).
    assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
    assert (SOKfl : store_ok rsegs m1 (wa (fs_flag FS 2 jj)) 1 = true)
      by (apply (wv_store_ok mc m1 (fs_flag FS 2 jj) 1);
          [ intros i Hi; replace (fs_flag FS 2 jj + i) with (fs_flag FS 2 jj) by lia;
            apply (cm_stk_wv mc FS (FS + FS_SIZE) (fs_flag FS 2 jj) FSPstk); unfold FS_SIZE in *; lia
          | exact WMc | lia | unfold FS_SIZE in *; lia ]).
    change (Z_to_bv 64 (fs_flag FS 2 jj)) with (wa (fs_flag FS 2 jj)).
    apply (wmono_write rsegs mc m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in WMc.
    apply (cm_shadow_rw_write m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in SRcur.
    apply (mem_inv_store rsegs m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) in Jmicur;
      [| rewrite length_le1; exact SOKfl].
    apply (stk_write rsegs m1 (Sp - 9136) Sp (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STwcur;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
    apply (munch_write _ mc m1 (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in MUc;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia
       | rewrite length_le1; cbn [inside]; right; right; left; split; lia].
    apply (stk_write rsegs m1 FS (FS + FS_SIZE) (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0))) in STfs1;
      [| unfold FS_SIZE in *; lia | rewrite length_le1; lia].
    assert (FRup : fr + 320 <= Sp) by lia.
    assert (SAFup : shadow_addr fr + 40 <= Sp - 104).
    { unfold shadow_addr, ASAN_K, HIGHMEM_BEG in *. Z.div_mod_to_equations. lia. }
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (SAVf : rw_cells rsegs mf (Sp + -104) cmSAVES)
        by (apply (rw_cells_transport rsegs _ mc mf (Sp + -104) cmSAVES SAV MUc WMc);
            cbn [disjoint_from cells_size csize];
            split; [right; lia | split; [right; lia | split; [right; lia | exact I]]]) end.
    clear SAV. unfold cmSAVES in SAVf.
    do 18 step.
    apply evtF_done. unfold cmPost. subst r.
    unfold aWc, aXs in Jmu.
    exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6. eexists.
    assert (FRin : fs_frame FS 2 0 <= fr /\ fr + 256 <= fs_frame FS 2 (fs_M 2)).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ 12) with 4096 in Hj. lia. }
    assert (FLin : fs_flag FS 2 0 <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= fs_flag FS 2 0 + fs_M 2).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 12) with 4096 in Hj. lia. }
    assert (INframe : In (fs_frame FS 2 0, fs_frame FS 2 (fs_M 2)) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (INflag : In (fs_flag FS 2 0, fs_flag FS 2 0 + fs_M 2) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (INsh : In (shadow_addr (fs_frame FS 2 0), shadow_addr (fs_frame FS 2 (fs_M 2))) (fp_w [0%nat;1%nat;2%nat] FS))
      by (apply in_flat_map; exists 2%nat; split; [cbn [In]; tauto | cbn [fp_w1 In]; tauto]).
    assert (SG1f : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr) by (apply acl_sh_ge; destruct FRin; lia).
    assert (SG2f : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
    { pose proof (cm_sh_add8 fr 32 Fm8) as E. replace (fr + 8 * 32) with (fr + 256) in E by lia. rewrite <- E.
      apply acl_sh_ge. destruct FRin; lia. }
    assert (SUB : sub_fp [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                          (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                    ([(Sp - 9136, Sp)] ++ fp_w [0%nat;1%nat;2%nat] FS
                       ++ [(shadow_addr (Sp - 9136), shadow_addr Sp)])).
    { intros x Hx. cbn [app outside] in Hx. destruct Hx as (_ & Hx2).
      apply fl_out_app_inv in Hx2 as (Hxfp & _). cbn [outside].
      split; [| split; [| split; [| exact I]]].
      - intros Hc. apply (out_in _ _ _ x Hxfp INframe). destruct FRin as (A1 & A2). lia.
      - intros Hc. apply (out_in _ _ _ x Hxfp INsh). lia.
      - intros Hc. apply (out_in _ _ _ x Hxfp INflag). destruct FLin as (B1 & B2). lia. }
    split; [reflexivity|].
    match goal with |- munch _ _ ?Mm /\ _ => set (M := Mm) in * end.
    split; [eapply (munch_trans _ m mc); [exact Jmu | eapply munch_weaken; [exact SUB | exact MUc]] |].
    split; [eapply (wmono_trans rsegs m mc); [exact Jwm | exact WMc] |].
    split; [exact Jmicur |].
    split; [exact STwcur |].
    split; [ eapply fl_asan_cells; [exact JAC | exact MUc |];
             intros x Hx; unfold RT_LO, RT_HI, ASAN_GT, ASAN_K in *; cbn [outside];
             split; [ clear -Hx AF3 FRlo; lia
                    | split; [ clear -Hx Fpos; unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia
                             | split; [ clear -Hx AF3 FLo; lia | exact I ] ] ] |].
    split; [exact SRcur |].
    assert (FLv : fs_flag FS 2 jj = FS + 28672 + jj)
      by (unfold fs_flag; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 15) with 32768; change (2 ^ 13) with 8192; lia).
    assert (M2 : fs_M 2 = 4096) by reflexivity.
    pose proof FRin as (FRa & FRb). pose proof FLin as (FLa & FLb).
    assert (BELh : forall x, FS <= x < FS + 36864 -> x <> fs_flag FS 2 jj ->
              outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x).
    { intros x Hx Hne. cbn [outside]. split; [lia | split; [| split; [lia | exact I]]].
      intros [A B]. apply (acl_app_not_shadow x); [apply AF5; unfold FS_SIZE in *; lia |].
      pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HS.
      replace (shadow_addr fr + (x - shadow_addr fr)) with x in HS by lia. exact HS. }
    assert (RDfl : mrd rsegs M (wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0)).
    { change (mrd rsegs (write_to_mem m1 (wa (fs_flag FS 2 jj)) (le1 (Z_to_bv 64 0))) (wa (fs_flag FS 2 jj))
              = Some (Z_to_bv 8 0)).
      pose proof (bytes_at_write_same rsegs m1 (fs_flag FS 2 jj) (le1 (Z_to_bv 64 0)) ltac:(lia)
                    ltac:(rewrite length_le1; unfold FS_SIZE in *; lia)) as BW.
      destruct BW as (_ & _ & BW). specialize (BW 0%nat ltac:(rewrite length_le1; lia)).
      replace (fs_flag FS 2 jj + Z.of_nat 0) with (fs_flag FS 2 jj) in BW by lia.
      rewrite BW. reflexivity. }
    assert (DJall : forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
              fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
                    (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
    { intros DT TS C T DB kk HT. pose proof (JTL DT TS C T DB kk HT) as JTLi. unfold aXs in JTLi.
      constructor; [| constructor; [| constructor; [| constructor]]]; cbn [fst snd].
      - apply (cm_dj_in _ _ (fs_frame FS 2 0) (fs_frame FS 2 (fs_M 2)) fr (fr + 8) JTLi);
          [apply in_or_app; left; exact INframe | lia | lia].
      - apply (cm_dj_in _ _ (shadow_addr (fs_frame FS 2 0)) (shadow_addr (fs_frame FS 2 (fs_M 2)))
                 (shadow_addr fr) (shadow_addr fr + 32) JTLi); [apply in_or_app; left; exact INsh | lia | lia].
      - apply (cm_dj_in _ _ (fs_flag FS 2 0) (fs_flag FS 2 0 + fs_M 2) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) JTLi);
          [apply in_or_app; left; exact INflag | lia | lia]. }
    split.
    { split; [unfold HIGHMEM_BEG in *; lia | split; [lia | split; [clear -HAE; unfold APPMEM_END in *; lia |]]].
      intros i Hi.
      pose proof (JAWX (Sp - 9136 + i) ltac:(lia) ltac:(lia)) as AB.
      pose proof (rt_app_shadow (Sp - 9136 + i) (proj1 AB)) as HS.
      apply (addr_byte_keep _ mc M (Sp - 9136 + i) AB MUc).
      cbn [outside]. split; [| split; [| split; [| exact I]]].
      - intros [A B]. apply (acl_app_not_shadow (shadow_addr (Sp - 9136 + i))); [apply AF5; lia | exact HS].
      - replace (shadow_addr fr + 32) with (shadow_addr (fr + 256))
          by (rewrite (cm_sh_div fr 256 Fm8); reflexivity).
        apply (acl_win_sh (Sp - 9136 + i) fr (fr + 256) Fm8). lia.
      - intros [A B]. apply (acl_app_not_shadow (shadow_addr (Sp - 9136 + i)));
          [apply AF5; unfold FS_SIZE in *; lia | exact HS]. }
    split.
    { destruct JFP as (DT & TS & C & T & DB & kk & HT & HTP & HP & H88 & H96 & HCL & HFSb & HAb & HWd & HDd).
      pose proof (DJall DT TS C T DB kk HT) as DJ.
      exists DT, TS, C, T, DB, kk.
      split; [eapply fl_tls_cells; [exact HT | exact MUc | exact DJ]|].
      split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite length_le8 in Hx;
               eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
      split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
               split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4 | exact STfs1]|].
      split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; rewrite length_le8 in Hx; apply BELh; lia]|].
      split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; cbn [length] in Hx; apply BELh; lia]|].
      split.
      { apply Forall_cons_iff in HCL as [HC0 HCL]. apply Forall_cons_iff in HCL as [HC1 HCL].
        apply Forall_cons_iff in HCL as [HC2 _].
        constructor; [exact (cm_cls_keep _ mc M 0%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC0)|].
        constructor; [exact (cm_cls_keep _ mc M 1%nat (fs_flag FS 2 jj) ltac:(lia) ltac:(lia) BELh MUc HC1)|].
        constructor; [exact (cm_cls_rel _ mc M jj Hj BELh MUc RDfl HC2) | constructor]. }
      split; [exact HFSb|]. split; [exact HAb|]. split; [exact HWd | exact HDd]. }
    intros DT TS C T DB k HTM.
    destruct JFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _).
    pose proof (JTL DT0 TS0 C0 T0 DB0 k0 HT0) as JTLi0.
    pose proof (DJall DT0 TS0 C0 T0 DB0 k0 HT0) as DJ0.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d ->
                   outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32);
                            (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] x)
                 (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. eapply fl_dj_out; [exact DJ0 | exact Hin | cbn [fst snd] in Hx; lia]. }
    destruct (fl_tls_same mc M _ (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTM MUc Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact JTLi0.
Qed.

(* The exit 0x850fc .. the return: the real-stack frame (nn = 0) by one run, the side-stack frame (nn = 1) as
   cm_pre_rel, the release store at 0x85194 (the flag byte fs_flag FS 2 jj := 0) and cm_post_rel. *)
Lemma cm_exit : forall fr sp2 jj nn mc r (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmJ fr sp2 jj nn mc ->
  evtF rsegs RNG cmPost
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850fc) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HJ.
  pose proof HJ as HJk.
  destruct HJ as (HFK & Jmu & Jwm & Jmi & JRT & JAWX & JEXT & STw & STf & SAV & FLG).
  destruct JRT as (JAC & JSR & JFP & JTL).
  pose proof (fk_facts fr sp2 jj nn HFK) as (Fm32 & Fpos & Fhi & Fwv & Fap & Fsh & Fsp2).
  pose proof (cm_fr_R fr sp2 jj nn HFK) as FRR.
  pose proof (cm_fr_rng fr sp2 jj nn HFK) as (RFR & RFS & _).
  pose proof CA_facts as (CAm & CAlo & CAhi).
  assert (Fm8 : fr mod 8 = 0) by (clear -Fm32; Z.div_mod_to_equations; lia).
  pose proof RS as RSb.
  destruct HFK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst nn.
    assert (SOKfr : store_ok rsegs mc (wa fr) 8 = true) by
      (apply (wv_store_ok mc mc fr 8);
        [ intros i Hi; apply (cm_stk_wv mc fr (fr + 192) (fr + i) STf); lia | apply wmono_refl | lia | lia ]).
    assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (shadow_addr fr + k)).
    { intros k Hk. rewrite <- (cm_sh_add8 fr k Fm8). apply rt_app_shadow. apply Fap. lia. }
    assert (SBlo : 0 <= shadow_addr fr) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 0) (SHIN 0 ltac:(lia))); lia).
    assert (SBhi : shadow_addr fr + 32 <= 2 ^ 64) by
      (pose proof (rt_shadow_bound (shadow_addr fr + 23) (SHIN 23 ltac:(lia))); lia).
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof JSR as SRcur.
    pose proof Jmi as Jmicur.
    pose proof (munch_refl [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] mc) as MUc.
    pose proof STw as STwcur.
    step. step. step.
    change (Z_to_bv 64 fr) with (wa fr).
    apply (wmono_write rsegs mc mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in WMc.
    apply (cm_shadow_rw_write mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in SRcur.
    apply (mem_inv_store rsegs mc (wa fr) (le8 (Z_to_bv 64 1172321806))) in Jmicur;
      [| rewrite length_le8; exact SOKfr].
    apply (munch_write _ mc mc fr (le8 (Z_to_bv 64 1172321806))) in MUc;
      [| lia | rewrite length_le8; lia | cbn [inside]; left; split; [lia | rewrite length_le8; lia]].
    apply (stk_write rsegs mc (Sp - 9136) Sp fr (le8 (Z_to_bv 64 1172321806))) in STwcur;
      [| lia | rewrite length_le8; lia].
    replace (if (0 =? 0)%Z then 0 else fr) with 0 by reflexivity.
    step. rewrite bv_eqb_refl. cbv iota.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (cm_rd_list m1 24 (shadow_addr fr) SBlo ltac:(lia)
        (fun i Hi => proj2 (cmSRT_R _ SRcur (shadow_addr fr + i) (FRR i ltac:(lia)) (SHIN i ltac:(lia)))))
        as (cs0 & Lcs & BSH) end.
    assert (LcsO : (24 = length cs0)%nat) by (symmetry; exact Lcs).
    shst fr mc 4. shst fr mc 5. shst fr mc 6. shst fr mc 7. shst fr mc 0. shst fr mc 1. shst fr mc 2. shst fr mc 3.
    shst fr mc 12. shst fr mc 13. shst fr mc 14. shst fr mc 15. shst fr mc 8. shst fr mc 9. shst fr mc 10. shst fr mc 11.
    shst fr mc 20. shst fr mc 21. shst fr mc 22. shst fr mc 23. shst fr mc 16. shst fr mc 17. shst fr mc 18. shst fr mc 19.
    assert (FRup : fr + 320 <= Sp) by lia.
    assert (SPhm : HIGHMEM_BEG <= Sp) by (unfold HIGHMEM_BEG in *; lia).
    assert (SAFup : shadow_addr fr + 24 <= Sp - 104)
      by (unfold shadow_addr, ASAN_K, HIGHMEM_BEG in *; Z.div_mod_to_equations; lia).
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (SAVf : rw_cells rsegs mf (Sp + -104) cmSAVES)
        by (apply (rw_cells_transport rsegs _ mc mf (Sp + -104) cmSAVES SAV MUc WMc);
            cbn [disjoint_from cells_size csize]; split; [right; lia | split; [right; lia | exact I]]) end.
    clear SAV. unfold cmSAVES in SAVf.
    do 17 step.
    apply evtF_done. unfold cmPost. subst r.
    unfold aWc, aXs in Jmu.
    exists u0, u1, u2, y1, y2, y3, y4, y5, y6, y7, u3, u4, u5, u6. eexists.
    assert (SUB : sub_fp [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                    ([(Sp - 9136, Sp)] ++ fp_w [0%nat; 1%nat; 2%nat] FS
                       ++ [(shadow_addr (Sp - 9136), shadow_addr Sp)])).
    { intros x Hx. cbn [app outside] in Hx. destruct Hx as (Hx1 & Hx2).
      apply fl_out_app_inv in Hx2. destruct Hx2 as (Hxfp & Hxsh).
      cbn [outside] in Hxsh. destruct Hxsh as (Hxsh & _).
      pose proof (acl_sh_ge fr (Sp - 9136) ltac:(lia)) as G1.
      pose proof (acl_sh_ge Sp (fr + 192) ltac:(lia)) as G2.
      replace (fr + 192) with (fr + 8 * 24) in G2 by lia.
      rewrite (cm_sh_add8 fr 24 Fm8) in G2.
      cbn [outside]. split; [| split; [| exact I]].
      - clear -Hx1 Fhi Fpos CAlo CAhi Ef. lia.
      - clear -Hxsh G1 G2. lia. }
    split; [reflexivity|].
    match goal with |- munch _ _ ?Mm /\ _ => set (M := Mm) in * end.
    split; [eapply (munch_trans _ m mc); [exact Jmu | eapply munch_weaken; [exact SUB | exact MUc]] |].
    split; [eapply (wmono_trans rsegs m mc); [exact Jwm | exact WMc] |].
    split; [exact Jmicur |].
    split; [exact STwcur |].
    split; [ eapply fl_asan_cells; [exact JAC | exact MUc |];
             intros x Hx; unfold RT_LO, RT_HI, HIGHMEM_BEG in *; cbn [outside];
             split; [ clear -Hx HHM CAlo Ef; lia
                    | split; [ clear -Hx Fpos; unfold shadow_addr, ASAN_K in *; Z.div_mod_to_equations; lia
                             | exact I ] ] |].
    split; [exact SRcur |].
    split.
    { symmetry in LcsO.
      assert (BSHf : bytes_at rsegs M (shadow_addr fr)
        (fold_left (fun l k => upd_bytes l k (le1 (Z_to_bv 64 0))) cm_ks cs0)) by exact BSH.
      assert (LF : length (fold_left (fun l k => upd_bytes l k (le1 (Z_to_bv 64 0))) cm_ks cs0) = 24%nat)
        by exact Lcs.
      assert (COV : forall q, 0 <= q < 24 -> mrd rsegs M (wa (shadow_addr fr + q)) = Some (Z_to_bv 8 0)).
      { intros q Hq. destruct BSHf as (_ & _ & HBf).
        specialize (HBf (Z.to_nat q) ltac:(rewrite LF; lia)).
        rewrite Z2Nat.id in HBf by lia. rewrite HBf.
        rewrite (nth_fold1 (le1 (Z_to_bv 64 0)) cm_ks (Z.to_nat q) cs0 eq_refl
                   ltac:(rewrite LcsO; lia) ltac:(intros kk Hkk; rewrite LcsO; apply cm_ks_bound; exact Hkk)).
        destruct (in_dec Nat.eq_dec (Z.to_nat q) cm_ks) as [_|Hn]; [reflexivity|].
        exfalso; apply Hn; apply cm_ks_cover; lia. }
      split; [unfold HIGHMEM_BEG in *; lia | split; [lia | split; [clear -HAE; unfold APPMEM_END in *; lia |]]].
      intros i Hi.
      assert (NOTFR : forall x, Sp - 9136 <= x < Sp -> ~ (fr <= x < fr + 192) -> addr_byte M x).
      { intros x Hxw Hxnf.
        pose proof (JAWX x Hxw Hxnf) as AB. pose proof (proj1 AB) as HApp.
        apply (addr_byte_keep [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] mc M); [exact AB | exact MUc |].
        pose proof (rt_app_shadow x HApp) as HS.
        unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in HS.
        cbn [outside]. split; [| split; [| exact I]].
        - intros [A _]. destruct HS as [[_ HSl]|[_ HSl]]; clear -A HSl HHM CAlo CAhi Ef;
            unfold HIGHMEM_BEG in *; lia.
        - replace (shadow_addr fr + 24) with (shadow_addr (fr + 192))
            by (rewrite (cm_sh_div fr 192 Fm8); reflexivity).
          apply (acl_win_sh x fr (fr + 192) Fm8 Hxnf). }
      destruct (Z_lt_le_dec (Sp - 9136 + i) fr) as [Lo|Lo];
        [| destruct (Z_lt_le_dec (Sp - 9136 + i) (fr + 192)) as [Inr|Hi2]].
      - apply NOTFR; lia.
      - split; [replace (Sp - 9136 + i) with (fr + (Sp - 9136 + i - fr)) by lia; apply Fap; lia |].
        exists (Z_to_bv 8 0). split.
        + replace (shadow_addr (Sp - 9136 + i)) with (shadow_addr fr + (Sp - 9136 + i - fr) / 8).
          2:{ rewrite <- (cm_sh_div fr (Sp - 9136 + i - fr) Fm8). f_equal. lia. }
          apply COV. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
        + unfold shadow_ok. left. vm_compute. reflexivity.
      - apply NOTFR; lia. }
    split.
    { destruct JFP as (DT & TS & C & T & DB & kk & HT & HTP & HP & H88 & H96 & HCL & HFSb & HAb & HWd & HDd).
      pose proof (JTL DT TS C T DB kk HT) as JTLi.
      assert (SG1 : shadow_addr (Sp - 9136) <= shadow_addr fr) by (apply acl_sh_ge; lia).
      assert (SG2 : shadow_addr fr + 24 <= shadow_addr Sp).
      { pose proof (acl_sh_ge Sp (fr + 192) ltac:(lia)) as G.
        replace (fr + 192) with (fr + 8 * 24) in G by lia. rewrite (cm_sh_add8 fr 24 Fm8) in G. exact G. }
      assert (BEL : forall x, FS <= x < FS + FS_SIZE ->
                 outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] x).
      { intros x Hx. cbn [outside]. split; [| split; [| exact I]].
        - clear -Hx HFSb FRup HHM CAlo CAhi Ef. lia.
        - intros [A B]. pose proof (SHIN (x - shadow_addr fr) ltac:(lia)) as HSx.
          replace (shadow_addr fr + (x - shadow_addr fr)) with x in HSx by lia.
          destruct HP as (_ & _ & _ & HPapp & _). exact (acl_app_not_shadow x (HPapp x Hx) HSx). }
      assert (DJ : fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                     (fp_tls (bv_unsigned tp) DT TS C T DB kk)).
      { pose proof HWd as HW'. unfold fp_dj in HW'. apply Forall_inv in HW'.
        apply Forall_app in HW' as [HWtls _].
        constructor; [| constructor; [| constructor]].
        - eapply Forall_impl; [| exact HWtls]. intros [a b] Hd. unfold ly_dj in *; cbn [fst snd] in *.
          clear -Hd FRup Fhi Fpos CAlo CAhi Ef HHM. lia.
        - unfold fp_dj in JTLi. eapply Forall_impl; [| exact JTLi]. intros [a b] Hd.
          unfold aXs in Hd. apply Forall_app in Hd as [_ Hd]. apply Forall_inv in Hd.
          unfold ly_dj in *; cbn [fst snd] in *. clear -Hd SG1 SG2. lia. }
      exists DT, TS, C, T, DB, kk.
      split; [eapply fl_tls_cells; [exact HT | exact MUc | exact DJ]|].
      split; [eapply fl_bytes; [exact HTP | exact MUc | intros x Hx; rewrite length_le8 in Hx;
               eapply fl_dj_out; [exact DJ | cbn [fp_tls In]; do 2 right; left; reflexivity | lia]]|].
      split; [unfold fs_place in *; destruct HP as (P1 & P2 & P3 & P4 & P5);
               split; [exact P1|]; split; [exact P2|]; split; [exact P3|]; split; [exact P4|];
               eapply (stk_transport rsegs _ mc M FS (FS + FS_SIZE));
                 [exact P5 | exact MUc | exact WMc | intros x Hx; left; apply BEL; exact Hx]|].
      split; [eapply fl_bytes; [exact H88 | exact MUc | intros x Hx; apply BEL; rewrite length_le8 in Hx;
               unfold FS_SIZE; lia]|].
      split; [eapply fl_bytes; [exact H96 | exact MUc | intros x Hx; apply BEL; cbn [length] in Hx;
               unfold FS_SIZE; lia]|].
      split; [exact (Forall_impl _ (fun c Hc => fl_cls _ mc M FS c BEL MUc Hc) HCL)|].
      split; [exact HFSb|]. split; [exact HAb|]. split; [exact HWd | exact HDd]. }
    intros DT TS C T DB k HTM.
    destruct JFP as (DT0 & TS0 & C0 & T0 & DB0 & k0 & HT0 & _ & _ & _ & _ & _ & _ & _ & HWd & _).
    pose proof (JTL DT0 TS0 C0 T0 DB0 k0 HT0) as JTLi0.
    assert (SG1 : shadow_addr (Sp - 9136) <= shadow_addr fr) by (apply acl_sh_ge; lia).
    assert (SG2 : shadow_addr fr + 24 <= shadow_addr Sp).
    { pose proof (acl_sh_ge Sp (fr + 192) ltac:(lia)) as G.
      replace (fr + 192) with (fr + 8 * 24) in G by lia. rewrite (cm_sh_add8 fr 24 Fm8) in G. exact G. }
    assert (DJ0 : fp_dj [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)]
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { pose proof HWd as HW'. unfold fp_dj in HW'. apply Forall_inv in HW'.
      apply Forall_app in HW' as [HWtls _].
      constructor; [| constructor; [| constructor]].
      - eapply Forall_impl; [| exact HWtls]. intros [a b] Hd. unfold ly_dj in *; cbn [fst snd] in *.
        clear -Hd FRup Fhi Fpos CAlo CAhi Ef HHM. lia.
      - unfold fp_dj in JTLi0. eapply Forall_impl; [| exact JTLi0]. intros [a b] Hd.
        unfold aXs in Hd. apply Forall_app in Hd as [_ Hd]. apply Forall_inv in Hd.
        unfold ly_dj in *; cbn [fst snd] in *. clear -Hd SG1 SG2. lia. }
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d ->
                   outside [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 24)] x)
                 (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0)).
    { apply Forall_forall. intros [a b] Hin x Hx. eapply fl_dj_out; [exact DJ0 | exact Hin | cbn [fst snd] in Hx; lia]. }
    destruct (fl_tls_same mc M _ (bv_unsigned tp) DT0 TS0 C0 T0 DB0 k0 DT TS C T DB k HT0 HTM MUc Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6).
    subst DT0 TS0 C0 T0 DB0 k0. exact JTLi0.
  - subst nn.
    pose proof (rf_flag2 jj Hj) as RFL.
    eapply evtF_cut;
      [exact (cm_pre_rel fr sp2 jj mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
                Er HJk)|].
    intros ms (m1 & -> & HAt).
    (* the release store sb zero, 0(a0) at 0x85194 *)
    destruct acl_fs as (AF1 & AF2 & AF3 & AF4 & AF5 & AF6).
    assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
    { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
    pose proof HAt as (_ & _ & _ & _ & _ & _ & STfs1).
    assert (SOKfl : store_ok rsegs m1 (wa (fs_flag FS 2 jj)) 1 = true)
      by (apply (wv_store_ok m1 m1 (fs_flag FS 2 jj) 1);
          [ intros i Hi; replace (fs_flag FS 2 jj + i) with (fs_flag FS 2 jj) by lia;
            apply (cm_stk_wv m1 FS (FS + FS_SIZE) (fs_flag FS 2 jj) STfs1); unfold FS_SIZE in *; lia
          | apply wmono_refl | lia | unfold FS_SIZE in *; lia ]).
    clear STfs1.
    change (Z_to_bv 64 (fs_flag FS 2 jj)) with (wa (fs_flag FS 2 jj)).
    step.
    exact (cm_post_rel fr sp2 jj mc m1 r x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
             Er HAt).
Qed.

(* The exit 0x850fc in the state cm_exit takes: the result r = want CM_T len fb in s4 and cmJ at the exit memory. *)
Definition cm_exit_at (ms : machine_state) : Prop :=
  exists (fr sp2 jj nn : Z) (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
    r = want CM_T len fb /\ cmJ fr sp2 jj nn mc /\
    ms = MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
                 (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x850fc) fc None mc (seg_rom rsegs).

Lemma cm_exit_at_intro : forall fr sp2 jj nn mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmJ fr sp2 jj nn mc ->
  cm_exit_at (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
                      (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6
                      (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
                 F (Z_to_bv 64 0x850fc) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HJ.
  exists fr, sp2, jj, nn, mc, r, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9, z10, z11,
    u3, u4, u5, u6.
  split; [exact Er|]. split; [exact HJ | reflexivity].
Qed.

Lemma cm_exit_at_post : forall ms, cm_exit_at ms -> evtF rsegs RNG cmPost ms.
Proof.
  intros ms (fr & sp2 & jj & nn & mc & r & x1 & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z5 &
             z6 & z9 & z10 & z11 & u3 & u4 & u5 & u6 & Er & HJ & ->).
  exact (cm_exit fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HJ).
Qed.

(* ============================ entry and header (0x84e40 -> join 0x84ee4 -> gate 0x84f88) ============================ *)

(* Every byte readable in mm is readable in mm'. *)
Definition rd_mono (mm mm' : word -> option byte) : Prop :=
  forall x : word, (exists b, mrd rsegs mm x = Some b) -> exists b, mrd rsegs mm' x = Some b.

Lemma cm_not_outside_in : forall W x, ~ outside W x -> exists r, In r W /\ fst r <= x < snd r.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; cbn in H; [exfalso; exact (H I)|].
  destruct (Z.le_gt_cases lo x); destruct (Z.lt_ge_cases x hi).
  - exists (lo, hi). split; [left; reflexivity | cbn; lia].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists r. split; [right; exact Hr | exact Hx].
  - destruct (IH x) as (r & Hr & Hx); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists r. split; [right; exact Hr | exact Hx].
Qed.

(* A run that wrote only W, after which every byte of W reads back, keeps every readable byte readable. *)
Lemma rd_mono_list : forall W mm mm', munch W mm mm' ->
  Forall (fun r => forall y, fst r <= y < snd r -> exists b, mrd rsegs mm' (wa y) = Some b) W -> rd_mono mm mm'.
Proof.
  intros W mm mm' Hm HFr x Hx. destruct (rc_outside_dec W (bv_unsigned x)) as [Ho|Ho].
  - unfold mrd in *. rewrite (Hm x Ho). exact Hx.
  - destruct (cm_not_outside_in W _ Ho) as (r & Hr & Hin). rewrite Forall_forall in HFr.
    pose proof (HFr r Hr (bv_unsigned x) Hin) as R. unfold wa in R. rewrite Z_to_bv_lit_self in R. exact R.
Qed.

Lemma stk_mono : forall mm mm' lo hi, stk rsegs mm lo hi -> wmono rsegs mm mm' -> rd_mono mm mm' ->
  stk rsegs mm' lo hi.
Proof.
  intros mm mm' lo hi (H1 & H2 & H) Hw Hr. split; [lia|]. split; [lia|].
  intros a Ha. destruct (H a Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma shadow_rw_mono : forall mm mm', cmSRT mm -> wmono rsegs mm mm' -> rd_mono mm mm' -> cmSRT mm'.
Proof.
  intros mm mm' H Hw Hr P HP a Pa Ha. destruct (H P HP a Pa Ha) as [Hv Hb]. split; [apply Hw, Hv | apply Hr, Hb].
Qed.

Lemma rd_of_bytes : forall mm A bs, bytes_at rsegs mm A bs ->
  forall y, A <= y < A + Z.of_nat (length bs) -> exists b, mrd rsegs mm (wa y) = Some b.
Proof.
  intros mm A bs (Ha & Hl & H) y Hy. pose proof (H (Z.to_nat (y - A)) ltac:(lia)) as E.
  replace (A + Z.of_nat (Z.to_nat (y - A))) with y in E by lia.
  destruct (nth_error bs (Z.to_nat (y - A))) as [v|] eqn:En; [exists v; exact E|].
  apply nth_error_None in En. lia.
Qed.

Lemma rd_of_stk : forall mm lo hi, stk rsegs mm lo hi ->
  forall y, lo <= y < hi -> exists b, mrd rsegs mm (wa y) = Some b.
Proof. intros mm lo hi (_ & _ & H) y Hy. exact (proj2 (H y Hy)). Qed.

Lemma cm_stk_sub : forall mm lo hi lo' hi', stk rsegs mm lo hi -> lo <= lo' -> hi' <= hi -> stk rsegs mm lo' hi'.
Proof. intros mm lo hi lo' hi' (H1 & H2 & H) A B. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

Lemma land_align32 : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551584 = x / 32 * 32.
Proof.
  intros x Hx.
  replace 18446744073709551584 with (Z.land (Z.lnot (Z.ones 5)) (Z.ones 64)) by reflexivity.
  rewrite Z.land_assoc, (Z.land_comm x), <- Z.land_assoc, (Z.land_ones x 64) by lia.
  rewrite Z.mod_small by lia. rewrite Z.land_comm, <- Z.ldiff_land, Z.ldiff_ones_r by lia.
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

Lemma bytes_ro : forall mm A c, bytes_at rsegs mm A (cbytes c) -> cell_wf c -> ro_cells rsegs mm A [c].
Proof. intros mm A c H Hw. split; [split; [exact Hw | exact I] | cbn [cells_bytes]; rewrite app_nil_r; exact H]. Qed.
Lemma bytes_ro8 : forall mm A v, bytes_at rsegs mm A (le8 v) -> ro_cells rsegs mm A [C8 v].
Proof. intros mm A v H. exact (bytes_ro mm A (C8 v) H I). Qed.
Lemma bytes_ro4 : forall mm A v, bytes_at rsegs mm A (le4 v) -> ro_cells rsegs mm A [C4 v].
Proof. intros mm A v H. exact (bytes_ro mm A (C4 v) H I). Qed.

(* fp survives a run that writes only W, the class bytes fp_w cs FS and the window's shadow: the thread cells and the
   header points FS+88/FS+96 are apart from all of these, the side stack stays readable, and the hint and the flag
   bytes read back as 0/1 at m' (as lib/A/Prog/RcAsanFPLib.v fl_fp_free). *)
Lemma fl_fp_free : forall cs mm mm' TP FS0 lo hi W D Wm,
  fp cs mm TP FS0 lo hi W D ->
  (forall DT TS C T DB k, asan_tls_cells mm TP DT TS C T DB k ->
     fp_dj (fp_tls TP DT TS C T DB k) (fp_w cs FS0 ++ [(shadow_addr lo, shadow_addr hi)])) ->
  munch Wm mm mm' -> wmono rsegs mm mm' ->
  sub_fp Wm (W ++ fp_w cs FS0 ++ [(shadow_addr lo, shadow_addr hi)]) ->
  (forall x, FS0 + 80 <= x < FS0 + 104 -> outside Wm x) ->
  (forall x, FS0 <= x < FS0 + FS_SIZE -> outside Wm x \/ exists b, mrd rsegs mm' (wa x) = Some b) ->
  (forall c, In c cs ->
     (exists h', bytes_at rsegs mm' (fs_hint FS0 c) (le8 h')) /\
     (exists flags', bytes_at rsegs mm' (fs_flag FS0 c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  fp cs mm' TP FS0 lo hi W D.
Proof.
  intros cs mm mm' TP FS0 lo hi W D Wm
    (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HApp & HWd & HDd)
    Htls MU WM Hs O88 HRD Hcls.
  pose proof (Htls DT TS C T DB k HT) as TLSdj.
  assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x) (fp_tls TP DT TS C T DB k)).
  { apply Forall_forall. intros [a bnd] Hin x Hx. apply Hs. apply fl_out_app.
    - exact (fl_dj_out W _ a bnd x HWd (in_or_app _ _ _ (or_introl Hin)) Hx).
    - exact (fl_dj_out_r _ _ a bnd x TLSdj Hin Hx). }
  cbn [fp_tls] in Hc.
  repeat (let O := fresh "O" in apply Forall_cons_iff in Hc; destruct Hc as [O Hc]; cbn [fst snd] in O).
  pose proof HCL as HCL'.
  destruct HT as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & T18
    & T19).
  exists DT, TS, C, T, DB, k.
  split.
  { unfold asan_tls_cells.
    split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [fl_cellO MU|]. split; [exact T6|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [destruct T11 as (tb & te & T11); exists tb, te; fl_cellO MU|].
    split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [fl_cellO MU|].
    split; [fl_cellO MU|]. split; [fl_cellO MU|]. split; [exact T18|]. fl_cellO MU. }
  split; [fl_cellO MU|].
  split.
  { destruct HP as (P1 & P2 & P3 & P4 & P5). split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
    split; [exact P4|]. exact (fl_stk Wm mm mm' FS0 (FS0 + FS_SIZE) P5 MU WM HRD). }
  split; [fl_cellO MU|].
  split; [fl_cellO MU|].
  split.
  { apply Forall_forall. intros c Hin.
    pose proof (proj1 (Forall_forall _ _) HCL' c Hin) as HCc. destruct HCc as (Hc6 & _).
    destruct (Hcls c Hin) as ((h' & Hh') & (flags' & Hf' & Hl' & HF')).
    split; [exact Hc6|]. exists h', flags'. split; [exact Hh'|]. split; [exact Hf'|]. split; [exact Hl' | exact HF']. }
  split; [exact HFS|]. split; [exact HApp|]. split; [exact HWd | exact HDd].
Qed.

(* B's state from the entry on is cmJ: A's cmInv (the frame geometry, the writes inside aWc, the runtime state, the
   saves, the flag word of a side-stack frame) with the window addressable outside the frame (AWX), the bytes outside
   the window that the run reads (EXT), the window and the frame readable and writable. *)
Definition cmInv (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop := cmJ fr sp2 jj nn mc.

(* Route (C): the transport the invariant carries. *)
Lemma cm_inv_srt : forall fr sp2 jj nn mc, cmInv fr sp2 jj nn mc -> cmSRT mc.
Proof. intros fr sp2 jj nn mc (_ & _ & _ & _ & (_ & SRg & _ & _) & _). exact SRg. Qed.

(* The register state at the gate (0x84f88, the first length test): s0 = Sp, s1 = CA, s2 = frame (0 on the real
   stack, fr on the side stack), s3 = f, s4 = len, s5 = ASAN_K, s7 = shadow_addr fr, s8 = fr, a2 = 50. *)
Definition cmKB (Q : machine_state -> Prop) : Prop :=
  forall (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
    cmInv fr sp2 jj nn mc ->
    evtF rsegs RNG Q
      (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
               ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
               rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
           F (Z_to_bv 64 0x84f88) fc None mc (seg_rom rsegs)).

(* The header's writes: the frame address at CA + 16, the three frame words at fr and their 24 shadow bytes. *)
Definition cmHF (fr : Z) : list ivl :=
  [(CA + 16, CA + 24); (fr, fr + 24); (shadow_addr fr, shadow_addr fr + 24)].

Lemma fpw3_in_shadow : forall FS0 c, In c [0%nat; 1%nat; 2%nat] ->
  In (shadow_addr (fs_frame FS0 c 0), shadow_addr (fs_frame FS0 c (fs_M c))) (fp_w [0%nat; 1%nat; 2%nat] FS0).
Proof.
  intros FS0 c Hc. apply in_flat_map. exists c. split; [exact Hc|]. cbn [fp_w1 In]. right; right; right; left; reflexivity.
Qed.

Lemma fpw3_in_hint : forall FS0 c, In c [0%nat; 1%nat; 2%nat] ->
  In (fs_hint FS0 c, fs_hint FS0 c + 8) (fp_w [0%nat; 1%nat; 2%nat] FS0).
Proof.
  intros FS0 c Hc. apply in_flat_map. exists c. split; [exact Hc|]. cbn [fp_w1 In]. left; reflexivity.
Qed.

Lemma fpw3_in_flag : forall FS0 c, In c [0%nat; 1%nat; 2%nat] ->
  In (fs_flag FS0 c 0, fs_flag FS0 c 0 + fs_M c) (fp_w [0%nat; 1%nat; 2%nat] FS0).
Proof.
  intros FS0 c Hc. apply in_flat_map. exists c. split; [exact Hc|]. cbn [fp_w1 In]. right; left; reflexivity.
Qed.

Lemma cm_fr_bounds : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> ASAN_GT <= fr /\ fr + 256 <= Sp.
Proof.
  intros fr sp2 jj nn FK. pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj). unfold FS_SIZE in FShi.
  destruct FK as [(Efr & Esp & Ej & En) | (Hj & Efr & Esp & En)]; subst fr.
  - split; unfold ASAN_GT; lia.
  - unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
    change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hj.
    change (2 ^ 12) with 4096 in Hj.
    unfold ASAN_GT in FSgt. split; unfold ASAN_GT; lia.
Qed.

Lemma cm_sub : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> sub_fp (cmHF fr) aWc.
Proof.
  intros fr sp2 jj nn FK x Hout.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  unfold aWc in Hout. cbn [outside] in Hout. destruct Hout as (Hw & Hxs).
  unfold aXs in Hxs. apply fl_out_app_inv in Hxs. destruct Hxs as (Hfpw & Hws).
  cbn [outside] in Hws. destruct Hws as (Hws & _).
  unfold cmHF. cbn [outside]. split; [|split; [|split; [|exact I]]].
  - clear -Hw CAlo CAhi. lia.
  - destruct FK as [(Efr & _ & _ & _) | (Hj & Efr & _ & _)]; subst fr.
    + clear -Hw CAlo CAhi. lia.
    + pose proof (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as HFin.
      unfold fs_frame, fs_B, fs_M in HFin, Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in HFin, Hj |- *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
      change (2 ^ 12) with 4096 in *. lia.
  - destruct FK as [(Efr & _ & _ & _) | (Hj & Efr & _ & _)]; subst fr.
    + assert (GE : shadow_addr (Sp - 9136) <= shadow_addr (CA - 192)) by (apply acl_sh_ge; lia).
      assert (LE : shadow_addr (CA - 192) + 24 <= shadow_addr Sp)
        by (unfold shadow_addr; Z.div_mod_to_equations; lia).
      clear -Hws GE LE. lia.
    + pose proof (out_in _ _ _ _ Hfpw (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as HFin.
      assert (GE : shadow_addr (fs_frame FS 2 0) <= shadow_addr (fs_frame FS 2 jj)).
      { apply acl_sh_ge. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 20) with 1048576. lia. }
      assert (LE : shadow_addr (fs_frame FS 2 jj) + 24 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
      { unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
        change (2 ^ 12) with 4096 in *. Z.div_mod_to_equations; lia. }
      clear -HFin GE LE. lia.
Qed.

(* A shadow byte is apart from any range made of application bytes. *)
Lemma sh_out_app : forall s a b, in_shadow s -> (forall z, a <= z < b -> app_mem z) -> ~ (a <= s < b).
Proof. intros s a b Hs Hab [H1 H2]. exact (acl_app_not_shadow s (Hab s ltac:(lia)) Hs). Qed.

(* An application byte apart from the header's two application ranges is apart from cmHF. *)
Lemma cmHF_out_pt : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> app_mem x ->
  ~ (CA + 16 <= x < CA + 24) -> ~ (fr <= x < fr + 24) -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hap H1 H2.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & _ & _ & _ & _ & _).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (_ & FRhi).
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  unfold cmHF. cbn [outside]. split; [exact H1|]. split; [exact H2|]. split; [|exact I].
  pose proof (acl_sh_out x fr (fr + 8 * 24) Hap ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Ho.
  rewrite (cm_sh_add8 fr 24 FR8) in Ho. exact Ho.
Qed.

(* A byte of the side stack's header [FS, FS + 36864) is apart from cmHF. *)
Lemma cmHF_out_side : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> FS <= x < FS + 36864 -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
  apply (cmHF_out_pt fr sp2 jj nn x FK Hap).
  - lia.
  - destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; subst fr.
    + lia.
    + unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 20) with 1048576. change (2 ^ 2) with 4.
      lia.
Qed.

(* A byte below the side stack (the image's cells) and its shadow byte are apart from aWc. *)
Lemma cm_lo_out : forall x, 0 <= x < ASAN_GT -> outside aWc x /\ outside aWc (shadow_addr x).
Proof.
  intros x Hx. destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END, ASAN_GT in *; left; lia).
  assert (Hw : x < Sp - 9136 \/ Sp <= x) by (left; unfold ASAN_GT in *; lia).
  assert (Hf : outside (fp_w [0%nat; 1%nat; 2%nat] FS) x) by (apply acl_out_fpw_lo; [lia | exact Hap]).
  split; [exact (acl_out_Wc x Hap Hw Hf) | exact (acl_out_Wc_sh x Hap Hf Hw)].
Qed.

Lemma cm_rt_out_Wc : forall x, RT_LO <= x < RT_HI -> outside aWc x.
Proof. intros x Hx. apply cm_lo_out. unfold RT_LO, RT_HI, ASAN_GT in *. lia. Qed.

(* The side stack's header word range [FS + 80, FS + 104) is apart from aWc. *)
Lemma cm_hdr_out_Wc : forall x, FS + 80 <= x < FS + 104 -> outside aWc x.
Proof.
  intros x Hx.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
  apply acl_out_Wc; [exact Hap | left; lia | ].
  cbn [fp_w flat_map fp_w1 app].
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
  change (2 ^ 14) with 16384. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096.
  change (2 ^ 15) with 32768. change (2 ^ 20) with 1048576.
  change (2 ^ 1) with 2. change (2 ^ 2) with 4. change (2 ^ 0) with 1.
  repeat first
    [ exact I
    | split; [ apply acl_sh_out; [ exact Hap | unfold FS_SIZE in *; lia | unfold FS_SIZE, APPMEM_END in *; lia ] | ]
    | split; [ intros [? ?]; unfold FS_SIZE in *; lia | ] ].
Qed.

(* A byte of the runtime's cells [RT_LO, RT_HI) is apart from cmHF. *)
Lemma cmHF_out_rt : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> RT_LO <= x < RT_HI -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & _).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  unfold RT_LO, RT_HI in Hx.
  assert (Hap : app_mem x) by (unfold app_mem, LOWMEM_END; left; lia).
  apply (cmHF_out_pt fr sp2 jj nn x FK Hap).
  - lia.
  - unfold ASAN_GT in FRgt. lia.
Qed.

(* The 13 saved registers [Sp - 104, Sp) are apart from cmHF. *)
Lemma cmHF_out_saves : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> Sp - 104 <= x < Sp -> outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
  pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  assert (Hap : app_mem x) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
  apply (cmHF_out_pt fr sp2 jj nn x FK Hap).
  - lia.
  - destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; subst fr.
    + lia.
    + unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in Hj.
      change (2 ^ 12) with 4096 in Hj. lia.
Qed.

(* The flag-pointer word [fr + 248, fr + 256) of a side-stack frame is apart from cmHF. *)
Lemma cmHF_out_flag : forall fr sp2 jj nn x, cmFK fr sp2 jj nn -> nn = 1 -> fr + 248 <= x < fr + 256 ->
  outside (cmHF fr) x.
Proof.
  intros fr sp2 jj nn x FK Enn Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _). unfold FS_SIZE in FShi.
  pose proof FK as FKc.
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)].
  - subst nn. discriminate Enn.
  - assert (FRlo : FS + 36864 <= fr).
    { rewrite Ef. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 20) with 1048576.
      change (2 ^ 2) with 4. lia. }
    assert (FRhi2 : fr + 256 <= FS + 11571200).
    { rewrite Ef. unfold fs_frame, fs_B, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
      change (2 ^ 20) with 1048576. change (2 ^ 2) with 4. change (2 ^ (14 - 2)) with 4096 in Hj.
      change (2 ^ 12) with 4096 in Hj. lia. }
    assert (Hap : app_mem x) by (apply FSapp; unfold FS_SIZE; lia).
    apply (cmHF_out_pt fr sp2 jj nn x FKc Hap); lia.
Qed.

(* The shadow byte of a window byte outside the frame is apart from cmHF. *)
Lemma cmHF_sh_awx : forall fr sp2 jj nn y, cmFK fr sp2 jj nn -> Sp - 9136 <= y < Sp -> ~ (fr <= y < fr + 192) ->
  outside (cmHF fr) (shadow_addr y).
Proof.
  intros fr sp2 jj nn y FK Hy Hyf.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & _ & _ & FAPP & _ & _).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'. pose proof HAE as HAE'. unfold APPMEM_END in HAE'.
  assert (Hap : app_mem y) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
  pose proof (rt_app_shadow y Hap) as Hsh.
  unfold cmHF. cbn [outside]. split; [|split; [|split; [|exact I]]].
  - apply (sh_out_app (shadow_addr y) (CA + 16) (CA + 24) Hsh).
    intros z Hz. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. right. lia.
  - apply (sh_out_app (shadow_addr y) fr (fr + 24) Hsh).
    intros z Hz. replace z with (fr + (z - fr)) by lia. apply FAPP. lia.
  - pose proof (acl_win_sh y fr (fr + 8 * 24) FR8 ltac:(lia)) as Ho.
    rewrite (cm_sh_add8 fr 24 FR8) in Ho. exact Ho.
Qed.

(* The bytes outside the window that the run reads survive writes inside aWc. *)
Lemma cm_EXT_keep : forall W mm mm', EXT mm -> munch W mm mm' -> sub_fp W aWc -> EXT mm'.
Proof.
  intros W mm mm' (E1 & E2 & E3 & E4 & E5) MU SUB.
  assert (LO : forall x, 0 <= x < ASAN_GT -> outside W x /\ outside W (shadow_addr x)).
  { intros x Hx. destruct (cm_lo_out x Hx) as (A1 & A2). split; apply SUB; assumption. }
  assert (LOb : forall A bs, bytes_at rsegs mm A bs -> A + Z.of_nat (length bs) <= ASAN_GT ->
                  bytes_at rsegs mm' A bs).
  { intros A bs HB HL. apply (fl_bytes W mm mm' A bs HB MU). intros x Hx. pose proof (proj1 HB).
    apply (LO x). lia. }
  assert (LOa : forall p n, addressable mm p n -> p + n <= ASAN_GT -> addressable mm' p n).
  { intros p n HA HL. apply (acl_addr_munch W mm mm' p n HA MU). intros i Hi. pose proof (proj1 HA).
    apply (LO (p + i)). lia. }
  split; [|split; [|split; [|split]]].
  - intros Hlen. destruct (E1 Hlen) as (EB & EA).
    assert (INd : In (f, f + 50) aDf)
      by (unfold aDf; destruct (Z.ltb_spec len 50) as [L|L]; [lia | left; reflexivity]).
    destruct (HF Hlen) as (_ & _ & _ & Hfw).
    assert (OUT : forall i, 0 <= i < 50 -> outside W (f + i) /\ outside W (shadow_addr (f + i))).
    { intros i Hi. pose proof (acl_app_in mm f 50 i EA Hi) as Hap.
      assert (Hw : f + i < Sp - 9136 \/ Sp <= f + i) by lia.
      pose proof (acl_out_fpw_d f (f + 50) (f + i) INd ltac:(lia)) as Hfo.
      split; apply SUB; [exact (acl_out_Wc _ Hap Hw Hfo) | exact (acl_out_Wc_sh _ Hap Hfo Hw)]. }
    split.
    + apply (fl_bytes W mm mm' f fb EB MU). intros x Hx. rewrite Hfb in Hx. change (Z.of_nat 50) with 50 in Hx.
      replace x with (f + (x - f)) by lia. apply (OUT (x - f)). lia.
    + apply (acl_addr_munch W mm mm' f 50 EA MU). intros i Hi. exact (proj2 (OUT i Hi)).
  - apply LOa; [exact E2 | unfold CM_T, ASAN_GT; lia].
  - apply LOb; [exact E3 | rewrite CM_TBL_len; unfold CM_T, ASAN_GT; lia].
  - apply LOa; [exact E4 | unfold REAC_CTRL_PARSE_BC, ASAN_GT; lia].
  - destruct E5 as (C1 & C2 & C3 & C4 & C5). unfold aCL.
    split; [|split; [|split; [|split]]];
      (apply LOb; [assumption | rewrite ?length_le8; cbn [length Z.of_nat Pos.of_succ_nat];
                                unfold REAL_BCMP, REAL_MEMCMP, GOT_CF, CF, ASAN_GT; lia]).
Qed.

Lemma cm_EXT0 : EXT m.
Proof.
  split; [|split; [|split; [|split]]].
  - intros Hlen. destruct (HF Hlen) as (_ & _ & HB & _). split; [exact HB | exact (proj1 (AFU Hlen))].
  - exact AT.
  - exact BT.
  - exact ABC.
  - exact (conj HBCMP (conj HMEMCMP (conj HGOT (conj HCF254 HCF255)))).
Qed.

(* The invariant survives the header run: writes land only in cmHF, which is inside aWc (cm_sub), the side stack's
   class bytes and the window's shadow (fl_fp_free). *)
Lemma cm_inv_step : forall fr sp2 jj nn mc mc',
  cmInv fr sp2 jj nn mc ->
  munch (cmHF fr) mc mc' -> wmono rsegs mc mc' -> rd_mono mc mc' -> mem_inv rsegs mc' ->
  cmInv fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' INV MU WM RM MI'.
  destruct INV as (FK & MUmc & WMmc & MImc & (ACmc & SRmc & FPg & TLg) & AWXg & EXTg & STWg & STFg & SVg & FLg).
  pose proof (cm_sub fr sp2 jj nn FK) as SUB.
  pose proof FPg as FPpack.
  destruct FPg as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTPle & HPl & H88 & H96 & HCL & HFSlo & HApphi & HWd & HDd).
  destruct HPl as (HP1 & HP2 & HP3 & HP4 & HPstk).
  split; [exact FK|].
  split; [exact (munch_trans aWc m mc mc' MUmc (munch_weaken (cmHF fr) aWc mc mc' SUB MU))|].
  split; [exact (wmono_trans rsegs m mc mc' WMmc WM)|].
  split; [exact MI'|].
  split.
  { split; [exact (fl_asan_cells (cmHF fr) mc mc' ACmc MU (fun x Hx => cmHF_out_rt fr sp2 jj nn x FK Hx))|].
    split; [exact (shadow_rw_mono mc mc' SRmc WM RM)|].
    split.
    { apply (fl_fp_free [0%nat; 1%nat; 2%nat] mc mc' (bv_unsigned tp) FS (Sp - 9136) Sp aWf aDf (cmHF fr)
               FPpack TLg MU WM).
      - unfold aWf, aWc, aXs. cbn [app]. exact SUB.
      - intros x Hx. apply (cmHF_out_side fr sp2 jj nn x FK). lia.
      - intros x Hx. right. apply RM. exact (rd_of_stk mc FS (FS + FS_SIZE) HPstk x Hx).
      - intros c Hc.
        pose proof (proj1 (Forall_forall _ _) HCL c Hc) as (Hc6 & h & flags & HH & HFf & HLn & HF01).
        split.
        + exists h. apply (fl_bytes (cmHF fr) mc mc' (fs_hint FS c) (le8 h) HH MU).
          intros x Hx. rewrite length_le8 in Hx. apply (cmHF_out_side fr sp2 jj nn x FK).
          unfold fs_hint in Hx. lia.
        + exists flags. split; [|split; [exact HLn | exact HF01]].
          apply (fl_bytes (cmHF fr) mc mc' (fs_flag FS c 0) flags HFf MU).
          intros x Hx. rewrite HLn in Hx. apply (cmHF_out_side fr sp2 jj nn x FK).
          unfold fs_flag, fs_M in Hx. destruct Hc as [E | [E | [E | []]]]; subst c;
            cbn [Z.of_nat Pos.of_succ_nat] in Hx.
          * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 0)) with 32768 in Hx.
            change (2 ^ (14 - 0)) with 16384 in Hx. lia.
          * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 1)) with 16384 in Hx.
            change (2 ^ (14 - 1)) with 8192 in Hx. lia.
          * change (2 ^ 15) with 32768 in Hx. change (2 ^ (15 - 2)) with 8192 in Hx.
            change (2 ^ (14 - 2)) with 4096 in Hx. lia. }
    intros DT TS C T DB kk HTcells'.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside (cmHF fr) x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUB. unfold aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLg DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same mc mc' (cmHF fr) (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells' MU Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLg DT TS C T DB kk HT0). }
  split.
  { intros x Hxw Hxf. apply (addr_byte_keep (cmHF fr) mc mc' x (AWXg x Hxw Hxf) MU).
    exact (cmHF_sh_awx fr sp2 jj nn x FK Hxw Hxf). }
  split; [exact (cm_EXT_keep (cmHF fr) mc mc' EXTg MU SUB)|].
  split; [exact (stk_mono mc mc' _ _ STWg WM RM)|].
  split; [exact (stk_mono mc mc' _ _ STFg WM RM)|].
  split.
  { apply (acl_rw (cmHF fr) mc mc' (Sp + -104) cmSAVES SVg MU WM).
    intros x Hx. apply (cmHF_out_saves fr sp2 jj nn x FK).
    unfold cmSAVES in Hx. cbn [cells_size csize] in Hx. lia. }
  intros Enn.
  apply (fl_bytes (cmHF fr) mc mc' (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) (FLg Enn) MU).
  intros x Hx. rewrite length_le8 in Hx. apply (cmHF_out_flag fr sp2 jj nn x FK Enn). lia.
Qed.

Ltac cm_wv :=
  let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
  match goal with
  | |- wview _ _ (wa ?x) <> None =>
    first
      [ match goal with H : forall a, _ -> wview rsegs m (wa a) <> None |- _ => apply H; lia end
      | match goal with H : forall k, 0 <= k < 192 -> wview rsegs m (wa (?fr + k)) <> None |- _ =>
          replace x with (fr + (x - fr)) by lia; apply H; lia end
      | match goal with H : forall k, 0 <= k < 24 -> wview rsegs m (wa (?s + k)) <> None |- _ =>
          replace x with (s + (x - s)) by lia; apply H; lia end ]
  end.

Ltac cm_wst a n :=
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      let HS := fresh "HS" in
      assert (HS : store_ok rsegs mm (wa a) n = true)
        by (eapply wv_store_ok;
            [ cm_wv | eassumption
            | try unfold ASAN_K; Z.div_mod_to_equations; lia
            | try unfold ASAN_K; Z.div_mod_to_equations; lia ])
  end.

(* The header run from the join 0x84ee4 to the gate 0x84f88: the sd s8 at CA + 16, the three frame words at fr, fr + 8,
   fr + 16, and the 24 shadow bytes at shadow_addr fr + 0..23; it reaches the gate in the cmKB register state and
   rebuilds the invariant at the written memory (cm_inv_step). *)
Lemma cm_header : forall (Q : machine_state -> Prop) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rs7 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
  cmKB Q -> cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 rs7 (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
         F (Z_to_bv 64 0x84ee4) fc None mc (seg_rom rsegs)).
Proof.
  intros Q fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs6 rs7 rs9 rs10 rs11 rt3 rt4 rt5 rt6 K INV.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof INV as INVk.
  destruct INV as (FK & MUg & WMg & MIg & (ACg & SRg & FPg & TLg) & AWXg & EXTg & STWg & STFg & SVg & FLg).
  clear MUg AWXg EXTg SVg FLg FPg TLg ACg.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSPc).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & _).
  pose proof RFS as RFS'. unfold shadow_addr in RFS'.
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  unfold shadow_addr in FSW.
  assert (cmSTW : forall a, Sp - 9136 <= a < Sp -> wview rsegs m (wa a) <> None)
    by (intros a Ha; exact (cm_stk_wv m _ _ _ ST Ha)).
  assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (fr / 8 + ASAN_K + k)).
  { intros k Hk. pose proof (rt_app_shadow (fr + 8 * k) (FAP (8 * k) ltac:(lia))) as H.
    rewrite (cm_sh_add8 fr k FR8) in H. unfold shadow_addr in H. exact H. }
  assert (SHlo : 0 <= fr / 8 + ASAN_K) by (pose proof (rt_shadow_bound _ (SHIN 0 ltac:(lia))); lia).
  assert (SHhi : fr / 8 + ASAN_K + 24 <= 2 ^ 64) by (pose proof (rt_shadow_bound _ (SHIN 23 ltac:(lia))); lia).
  assert (STSH : stk rsegs mc (fr / 8 + ASAN_K) (fr / 8 + ASAN_K + 24)).
  { split; [lia|]. split; [lia|]. intros a Ha.
    replace a with (fr / 8 + ASAN_K + (a - (fr / 8 + ASAN_K))) by lia.
    apply (cm_srw_fr fr sp2 jj nn mc _ FK SRg); [unfold shadow_addr; lia | apply SHIN; lia]. }
  clear SRg.
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  unfold cmHF, shadow_addr in MUh.
  cm_wst (CA + 16) 8%nat. step. store_done.
  do 3 step.
  step. rewrite (unsigned_lit fr) by lia. rewrite rc_shr3.
  do 6 step.
  cm_wst fr 8%nat. step. store_done.
  cm_wst (fr + 8) 8%nat. step. store_done.
  cm_wst (fr + 16) 8%nat. step. store_done.
  step. step.
  cm_wst (fr / 8 + ASAN_K) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 1) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 2) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 3) 1%nat. step. store_done.
  step.
  cm_wst (fr / 8 + ASAN_K + 4) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 5) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 6) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 7) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 8) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 9) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 10) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 11) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 12) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 13) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 14) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 15) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 20) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 21) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 22) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 23) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 16) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 17) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 18) 1%nat. step. store_done.
  cm_wst (fr / 8 + ASAN_K + 19) 1%nat. step. store_done.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (RMh : rd_mono mc mf)
      by (apply (rd_mono_list _ mc mf MUh); repeat constructor; cbn [fst snd]; intros y Hy;
          [ apply (rd_of_stk _ _ _ STWg); lia
          | apply (rd_of_stk _ _ _ STFg); lia
          | apply (rd_of_stk _ _ _ STSH); lia ]) end.
  eapply K.
  eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* After the class-2 frame request, the flag byte j reads 1 and the rest of the class-2 flag array is kept: the whole
   array reads back as a list of 0/1 bytes of length fs_M 2. *)
Lemma cm_flag_upd : forall (ms mc : word -> option byte) (W : list ivl) (flags : list byte) (j : Z),
  0 <= j < fs_M 2 -> Z.of_nat (length flags) = fs_M 2 ->
  Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags ->
  bytes_at rsegs ms (fs_flag FS 2 0) flags -> munch W ms mc ->
  (forall x, fs_flag FS 2 0 <= x < fs_flag FS 2 0 + fs_M 2 -> x <> fs_flag FS 2 j -> outside W x) ->
  bytes_at rsegs mc (fs_flag FS 2 j) [Z_to_bv 8 1] ->
  exists flags', bytes_at rsegs mc (fs_flag FS 2 0) flags' /\ Z.of_nat (length flags') = fs_M 2 /\
     Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags'.
Proof.
  intros ms mc W flags j Hj Hlen HF01 HFa MU Hout HFL.
  assert (EFj : fs_flag FS 2 j = fs_flag FS 2 0 + j) by (unfold fs_flag; lia).
  assert (RD : mrd rsegs mc (wa (fs_flag FS 2 0 + j)) = Some (Z_to_bv 8 1)).
  { destruct HFL as (_ & _ & HB). specialize (HB 0%nat ltac:(cbn [length]; lia)).
    cbn [Z.of_nat] in HB. rewrite Z.add_0_r in HB. rewrite <- EFj. exact HB. }
  exists (upd_bytes flags (Z.to_nat j) [Z_to_bv 8 1]).
  split; [|split].
  - apply (cm_bytes_upd1 W ms mc (fs_flag FS 2 0) flags j (Z_to_bv 8 1) HFa MU); [lia | | exact RD].
    intros x Hx Hne. apply Hout; lia.
  - rewrite upd_bytes_length by (cbn [length]; lia). exact Hlen.
  - apply cm_forall_upd; [exact HF01 | constructor; [right; reflexivity | constructor]].
Qed.

(* Build cmInv at the join from: the frame facts, the run's writes Wm (inside aWc) apart from the shadow of the window
   outside the frame, the class hint/flag readback, the frame readable and writable, the saves and (side-stack
   frame) the flag word. The runtime state is rebuilt by fl_fp_free / fl_tls_same, the window by addr_byte_keep. *)
Lemma cm_mk_inv : forall (fr sp2 jj nn : Z) (mc : word -> option byte) (Wm : list ivl),
  cmFK fr sp2 jj nn ->
  munch Wm m mc -> wmono rsegs m mc -> rd_mono m mc -> mem_inv rsegs mc ->
  sub_fp Wm aWc ->
  (forall y, Sp - 9136 <= y < Sp -> ~ (fr <= y < fr + 192) -> outside Wm (shadow_addr y)) ->
  (forall c, In c [0%nat; 1%nat; 2%nat] ->
     (exists h', bytes_at rsegs mc (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs mc (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  stk rsegs mc fr (fr + 192) ->
  rw_cells rsegs mc (Sp + -104) cmSAVES ->
  (nn = 1 -> bytes_at rsegs mc (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) ->
  cmInv fr sp2 jj nn mc.
Proof.
  intros fr sp2 jj nn mc Wm FK MUw WMw RMw MIw SUBw SHW Hcls STFw SAVESmc FLAGmc.
  pose proof FP0 as FPpack0.
  pose proof FP0 as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTP0 & HPl0 & H880 & H960 & HCL0 & HFS0 & HApp0 & HWd0
    & HDd0).
  pose proof HPl0 as (P1 & P2 & P3 & P4 & P5).
  split; [exact FK|].
  split; [exact (munch_weaken Wm aWc m mc SUBw MUw)|].
  split; [exact WMw|].
  split; [exact MIw|].
  split.
  { split; [exact (fl_asan_cells Wm m mc AC MUw (fun x Hx => SUBw x (cm_rt_out_Wc x Hx)))|].
    split; [exact (shadow_rw_mono m mc cmSRT_refl WMw RMw)|].
    split.
    { apply (fl_fp_free [0%nat; 1%nat; 2%nat] m mc (bv_unsigned tp) FS (Sp - 9136) Sp aWf aDf Wm FPpack0 TLS0
               MUw WMw).
      - exact SUBw.
      - intros x Hx. apply SUBw. exact (cm_hdr_out_Wc x Hx).
      - intros x Hx. right. apply RMw. exact (rd_of_stk m FS (FS + FS_SIZE) P5 x Hx).
      - exact Hcls. }
    intros DT TS C T DB kk HTcells.
    assert (apart : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                      (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUBw. unfold aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd0 (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLS0 DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same m mc Wm (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells MUw apart)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLS0 DT TS C T DB kk HT0). }
  split.
  { intros x Hxw Hxf. apply (addr_byte_keep Wm m mc x); [| exact MUw | exact (SHW x Hxw Hxf)].
    pose proof AW as (_ & _ & _ & AWb). replace x with (Sp - 9136 + (x - (Sp - 9136))) by lia. apply AWb. lia. }
  split; [exact (cm_EXT_keep Wm m mc cm_EXT0 MUw SUBw)|].
  split; [exact (stk_mono m mc _ _ ST WMw RMw)|].
  split; [exact STFw|].
  split; [exact SAVESmc|].
  exact FLAGmc.
Qed.

(* A side-stack header byte (a hint or flag of class 0/1/2) is apart from the side-arm writes: the data ranges by lia,
   the frame's shadow range by acl_sh_out (application byte against shadow). *)
Ltac cm_hdr_out HFSapp HHm8 :=
  cbn [outside]; unfold fs_hint, fs_flag, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in *
               | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in *
               | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in *
               | change (2 ^ (15 - 2)) with 8192 in *
               | change (2 ^ 14) with 16384 in *
               | change (2 ^ 13) with 8192 in *
               | change (2 ^ 12) with 4096 in * ];
  repeat split; try exact I;
  first
    [ lia
    | match goal with
      | |- ~ (shadow_addr ?frr <= ?xx < _) =>
          let A := fresh "A" in let B := fresh "B" in intros [A B];
          pose proof (acl_sh_out xx frr (frr + 8 * 32) ltac:(apply HFSapp; unfold FS_SIZE; lia)
                        ltac:(lia) ltac:(unfold APPMEM_END; lia)) as Hso;
          rewrite (cm_sh_add8 frr 32 HHm8) in Hso; apply Hso; split; [exact A | exact B]
      end ].

(* The memory at the class-2 frame request (0x84eb0 calls __asan_stack_malloc_2 at 0x3d9f8, return 0x84eb4): the
   entry's writes are inside the window, the window and the 13 saves are readable and writable, mem_inv holds.  The
   call's other premises follow from these and the Section's premises. *)
Definition cmAtSM2 (m0 : word -> option byte) : Prop :=
  munch [(Sp - 9136, Sp)] m m0 /\ wmono rsegs m m0 /\ mem_inv rsegs m0 /\ stk rsegs m0 (Sp - 9136) Sp /\
  rw_cells rsegs m0 (Sp + -104) cmSAVES.

(* The side arm of the request's post (asan_stack_malloc_post 2 ASAN_STACK_MALLOC_K at this call): the return state
   with ra, sp and s0..s11 those of the call; wmono, mem_inv and the window below CA; the side stack readable and
   writable; the class-2 hint word; the frame j.  The frame clause is asan_stack_malloc_frame 2 ASAN_STACK_MALLOC_K
   (Z_to_bv 64 CA) 192 FS j a0' m0 m2 written out at this call WITHOUT two of its conjuncts: the real-stack word
   `bytes_at m2 (fr + 24) (le8 CA)` and `addressable m2 fr 192`.  Neither is used anywhere in this file, and neither
   has a source in the world form: cgif's astack_malloc_realizes (Reusable/YG0d.v:285-300) and a Theorem Labs lane's
   ctl_fs_of_astack_stmt do not give the real-stack word, and the auditor's own measurement marks both
   IN-FOOTPRINT (vacuous) - "can be dropped from the bridge" (a Theorem Labs lane's group B1 (munch-consumers.md section 1 (a working note, not in this delivery)),
   rows H24 and HADD).  Not in it either: the search facts on the index and fs_place's other conjuncts. *)
Definition cm_fs_post_2 (m0 : word -> option byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m2 : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 544436) (Z_to_bv 64 CA) gp tp t0' t1' t2' (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                  a0' a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                  s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc (Z_to_bv 64 544436)) fc None m2 (seg_rom rsegs) /\
    wmono rsegs m0 m2 /\ mem_inv rsegs m2 /\ stk rsegs m2 (Sp - 9136) CA /\
    stk rsegs m2 FS (FS + FS_SIZE) /\
    (exists h', bytes_at rsegs m2 (fs_hint FS 2) (le8 h')) /\
    (exists j, 0 <= j < fs_M 2 /\
       a0' = Z_to_bv 64 (fs_frame FS 2 j) /\ fs_frame FS 2 j mod 64 = 0 /\
       bytes_at rsegs m2 (fs_flag FS 2 j) [Z_to_bv 8 1] /\
       bytes_at rsegs m2 (fs_frame FS 2 j + 256 - 8) (le8 (Z_to_bv 64 (fs_flag FS 2 j))) /\
       bytes_at rsegs m2 (shadow_addr (fs_frame FS 2 j)) (repeat (Z_to_bv 8 0) (Z.to_nat 32)) /\
       stk rsegs m2 (fs_frame FS 2 j) (fs_frame FS 2 j + 256) /\
       (forall a, fs_frame FS 2 j <= a < fs_frame FS 2 j + 256 -> app_mem a) /\
       FS <= fs_frame FS 2 j /\ fs_frame FS 2 j + 256 <= FS + FS_SIZE /\ ASAN_GT <= fs_frame FS 2 j /\
       fs_frame FS 2 j + 256 <= CA - ASAN_STACK_MALLOC_K /\
       (forall (c' : nat) (j' : Z), (c' <= 10)%nat -> 0 <= j' < fs_M c' -> (c' <> 2%nat \/ j' <> j) ->
          fs_frame FS c' j' + fs_B c' <= fs_frame FS 2 j \/
          fs_frame FS 2 j + 256 <= fs_frame FS c' j') /\
       munch [(fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 j, fs_flag FS 2 j + 1);
              (fs_frame FS 2 j + 24, fs_frame FS 2 j + 32);
              (fs_frame FS 2 j + 256 - 8, fs_frame FS 2 j + 256);
              (shadow_addr (fs_frame FS 2 j), shadow_addr (fs_frame FS 2 j) + 32);
              (CA - ASAN_STACK_MALLOC_K, CA)] m0 m2).

(* The stretch from the entry 0x84e40 to the class-2 frame request: the 128-byte frame with the 13 saves at
   [Sp - 104, Sp), the aligned frame pointer CA, the loads of ASAN_K and of the flag word 1, a0 = 192. *)
Lemma cm_pre_sm2 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evtF rsegs RNG
    (fun ms => exists m0, ms =
       MS (mkR (Z_to_bv 64 544436) (Z_to_bv 64 CA) gp tp t0 t1 t2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
               (Z_to_bv 64 192) (wa 693944) (sx32 (wa 1)) a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 252408) fc None m0 (seg_rom rsegs) /\ cmAtSM2 m0)
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  unfold REAC_BOX_CATALOGUE_MATCH.
  (* The stores rewrite every hypothesis on the current memory; keep the section's premises on m for the join. *)
  pose proof ST as ST0. pose proof ST as STW. pose proof MI as MI0.
  clear ST BT HBCMP HMEMCMP HGOT HCF254 HCF255 MI.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  pose proof AC as (CK & GCK & _ & _ & _ & UA & GUA & _).
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
  apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
  assert (MU : munch [(Sp - 9136, Sp)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  carve_frame 104%nat ST0.
  step.
  assert (HSz : store_ok rsegs m (wa (Sp - 128)) 8 = true)
    by (eapply wv_store_ok; [intros i Hi; apply (cm_stk_wv m (Sp - 9136) (Sp + -104)); [exact ST0 | lia] |
        apply wmono_refl | lia | lia]).
  step. store_done.
  do 13 step.
  step. step.
  assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (Sp + -128))) 18446744073709551584 = CA).
  { rewrite unsigned_lit by lia. rewrite land_align32 by lia. unfold CA.
    replace (Sp + -128) with (Sp - 128) by lia. reflexivity. }
  rewrite EA.
  do 10 step.
  replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
  step. step.
  apply evtF_done. cbv beta. eexists. split; [reflexivity|].
  exact (conj MU (conj WM (conj MI0 (conj STW FR)))).
Qed.

(* The real-stack arm of the request's post (a0 = 0, every class-2 frame in use): the page probe at CA - 4096, the
   real-stack frame CA - 192, cmInv (cm_mk_inv) and the header (cm_header) to the gate. *)
Lemma cm_post_sm2_real : forall (Q : machine_state -> Prop) (m0 m2 : word -> option byte)
    (u0 u1 u2 x0 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
  cmKB Q -> cmAtSM2 m0 ->
  wmono rsegs m0 m2 -> mem_inv rsegs m2 -> stk rsegs m2 (Sp - 9136) CA -> stk rsegs m2 FS (FS + FS_SIZE) ->
  (exists h', bytes_at rsegs m2 (fs_hint FS 2) (le8 h')) ->
  x0 = Z_to_bv 64 0 -> munch [(fs_hint FS 2, fs_hint FS 2 + 8); (CA - ASAN_STACK_MALLOC_K, CA)] m0 m2 ->
  evtF rsegs RNG Q
    (MS (mkR (Z_to_bv 64 544436) (Z_to_bv 64 CA) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             x0 x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K) s6 s7 s8 s9 s10 s11
             u3 u4 u5 u6)
        F (ret_pc (Z_to_bv 64 544436)) fc None m2 (seg_rom rsegs)).
Proof.
  intros Q m0 m2 u0 u1 u2 x0 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 K HAt WM2 MI2 ST2 FQstk (h2 & HH2') Ex0 MUf.
  destruct HAt as (MU & WM & MI0 & STW & FR).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  replace (ret_pc (Z_to_bv 64 544436)) with (Z_to_bv 64 544436)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step. step. step.
  pose proof acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  pose proof FP0 as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & _ & _ & _ & HCLx & _).
  pose proof HCLx as HCLy.
  apply Forall_cons_iff in HCLy as [(_ & h0 & flags0 & HH0 & HF0 & HFl0 & HFb0) HCLy1].
  apply Forall_cons_iff in HCLy1 as [(_ & h1 & flags1 & HH1 & HF1 & HFl1 & HFb1) HCLy2].
  apply Forall_cons_iff in HCLy2 as [(_ & h2m & flags2m & HH2m & HF2m & HFl2m & HFb2m) _].
    subst x0.
    replace (negb (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0))) with false by reflexivity. cbv iota.
    unfold ASAN_STACK_MALLOC_K in MUf.
    assert (STW2 : stk rsegs m2 (Sp - 9136) Sp).
    { apply (fl_stk _ m0 m2 _ _ STW MUf WM2). intros x Hx.
      destruct (Z_lt_le_dec x (CA - 208)) as [L|L]; [|destruct (Z_lt_le_dec x CA) as [L2|L2]].
      - left. cbn [outside]. unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat]. split; [lia | split; [lia | exact I]].
      - right. apply (rd_of_stk _ _ _ ST2). lia.
      - left. cbn [outside]. unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat]. split; [lia | split; [lia | exact I]]. }
    assert (FR2 : rw_cells rsegs m2 (Sp + -104) cmSAVES).
    { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MUf WM2).
      cbn [disjoint_from cells_size csize Nat.add cmSAVES]. unfold fs_hint. repeat split; lia. }
    assert (WMr : wmono rsegs m m2) by (apply (wmono_trans _ _ _ _ WM WM2)).
    assert (MUr : munch [(Sp - 9136, Sp); (fs_hint FS 2, fs_hint FS 2 + 8)] m m2).
    { apply (munch_trans _ m m0 m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *.
        destruct Hx as (Hw & _). split; [exact Hw | exact I].
      - eapply munch_weaken; [|exact MUf]. intros x Hx. cbn [outside] in *.
        destruct Hx as (Hw & Hh & _). split; [exact Hh | split; [clear -Hw CAlo CAhi; lia | exact I]]. }
    clear MUf.
    unfold fs_hint in HH2'. cbn [Z.of_nat Pos.of_succ_nat] in HH2'.
    step. step.
    match goal with |- context [Z.land ?x 18446744073709551584] =>
      replace (Z.land x 18446744073709551584) with (CA - 192)
        by (rewrite ?(unsigned_lit CA), ?unsigned_lit by lia; rewrite land_align32 by lia;
            Z.div_mod_to_equations; lia) end.
    step. step.
    rewrite (unsigned_lit CA) by lia.
    assert (HSz2 : store_ok rsegs m2 (wa (CA - 4096)) 8 = true)
      by (eapply wv_store_ok;
          [intros i Hi; apply (cm_stk_wv m2 (Sp - 9136) CA); [exact ST2 | lia] | apply wmono_refl | lia | lia]).
    step. store_done.
    step.
    rewrite (rc_lts_signed (CA - 192) (CA - 4096)) by lia.
    replace (CA - 192 <? CA - 4096) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
    step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (RMr : rd_mono m mf)
        by (apply (rd_mono_list _ m mf MUr); repeat constructor; cbn [fst snd]; intros y Hy;
            [ apply (rd_of_stk _ _ _ STW2); lia
            | apply (rd_of_stk _ _ _ FQstk); unfold fs_hint in Hy; cbn [Z.of_nat Pos.of_succ_nat] in Hy;
              unfold FS_SIZE; lia ]) end.
    eapply (cm_header Q (CA - 192) (CA - 192) 0 0 _); [exact K|].
    apply (cm_mk_inv (CA - 192) (CA - 192) 0 0 _ [(Sp - 9136, Sp); (fs_hint FS 2, fs_hint FS 2 + 8)]).
    + left. split; [reflexivity | split; [reflexivity | split; reflexivity]].
    + exact MUr.
    + exact WMr.
    + exact RMr.
    + exact MI2.
    + intros x Hx. unfold aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hw & Hxs).
      unfold aXs in Hxs. apply fl_out_app_inv in Hxs. destruct Hxs as (Hfpw & _).
      cbn [outside]. split; [exact Hw | split; [|exact I]].
      exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))).
    + intros y Hy _.
      assert (Hap : app_mem y) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
      pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [outside]. split; [|split; [|exact I]].
      * unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        clear -Hsh Hy HHM'. lia.
      * apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
        intros z Hz. apply FSapp. unfold fs_hint in *. cbn [Z.of_nat Pos.of_succ_nat] in *. unfold FS_SIZE. lia.
    + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
      * split.
        -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (le8 h0) HH0 MUr).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cbn [outside]. unfold fs_hint in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
           split; [lia | split; [lia | exact I]].
        -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
           apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUr).
           intros x Hx. rewrite HFl0 in Hx. cbn [outside].
           unfold fs_flag, fs_M, fs_hint in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 0)) with 32768 in *;
             change (2 ^ (14 - 0)) with 16384 in *.
           split; [lia | split; [lia | exact I]].
      * split.
        -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (le8 h1) HH1 MUr).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cbn [outside]. unfold fs_hint in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
           split; [lia | split; [lia | exact I]].
        -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
           apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUr).
           intros x Hx. rewrite HFl1 in Hx. cbn [outside].
           unfold fs_flag, fs_M, fs_hint in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 1)) with 16384 in *;
             change (2 ^ (14 - 1)) with 8192 in *.
           split; [lia | split; [lia | exact I]].
      * split.
        -- exists h2. unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat]. exact HH2'.
        -- exists flags2m. split; [|split; [exact HFl2m | exact HFb2m]].
           apply (fl_bytes _ m _ (fs_flag FS 2 0) flags2m HF2m MUr).
           intros x Hx. rewrite HFl2m in Hx. cbn [outside].
           unfold fs_flag, fs_M, fs_hint in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *;
             change (2 ^ (14 - 2)) with 4096 in *.
           split; [lia | split; [lia | exact I]].
    + apply (cm_stk_sub _ (Sp - 9136) Sp); [exact STW2 | lia | lia].
    + exact FR2.
    + intros Hcontra; discriminate Hcontra.
Qed.

(* The side arm of the request's post (cm_fs_post_2: a0 = fs_frame FS 2 j): cmInv at the frame fs_frame FS 2 j
   (cm_mk_inv) and the header (cm_header) to the gate. *)
Lemma cm_post_sm2_side : forall (Q : machine_state -> Prop) (m0 : word -> option byte) (ms' : machine_state),
  cmKB Q -> cmAtSM2 m0 -> cm_fs_post_2 m0 ms' -> evtF rsegs RNG Q ms'.
Proof.
  intros Q m0 ms' K HAt PO.
  destruct HAt as (MU & WM & MI0 & STW & FR).
  destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E &
                  WM2 & MI2 & ST2 & FQstk & (h2 & HH2') & (jj & Hjj & FRM)).
  subst ms'.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  (* the class-2 flag array at the call memory m0 *)
  pose proof (fl_fp [0%nat;1%nat;2%nat] m m0 (bv_unsigned tp) FS (Sp - 9136) Sp [] aDf
                [(Sp - 9136, Sp)] FP0 MU WM ltac:(intros x Hx; exact Hx)) as FP1.
  destruct FP1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HCL1 & _).
  pose proof HCL1 as HCL1'. do 2 apply Forall_cons_iff in HCL1' as [_ HCL1']. apply Forall_cons_iff in HCL1' as [HC2 _].
  destruct HC2 as (_ & h & flags & HH2 & HF2 & HFl2 & HFb2).
  replace (ret_pc (Z_to_bv 64 544436)) with (Z_to_bv 64 544436)
    by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  step. step. step. step.
  pose proof acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold ASAN_GT in FSgt. unfold FS_SIZE in FShi.
  pose proof FP0 as (DTx & TSx & Cx & Tx & DBx & kkx & _ & _ & _ & _ & _ & HCLx & _).
  pose proof HCLx as HCLy.
  apply Forall_cons_iff in HCLy as [(_ & h0 & flags0 & HH0 & HF0 & HFl0 & HFb0) HCLy1].
  apply Forall_cons_iff in HCLy1 as [(_ & h1 & flags1 & HH1 & HF1 & HFl1 & HFb1) HCLy2].
  apply Forall_cons_iff in HCLy2 as [(_ & h2m & flags2m & HH2m & HF2m & HFl2m & HFb2m) _].
    destruct FRM as (Ex0 & Hm64 & HFL & Hflagword & HSH & STF & APF & FSlo & FShi' & GT & FRA' & DIS & MU2).
    remember (fs_frame FS 2 jj) as fr eqn:Efr.
    subst x0.
    unfold FS_SIZE in FShi'. change (fs_M 2) with 4096 in Hjj.
    unfold ASAN_STACK_MALLOC_K in MU2, FRA'.
    replace (fr + 256 - 8) with (fr + 248) in * by lia.
    assert (Hm8 : fr mod 8 = 0) by (clear -Hm64; Z.div_mod_to_equations; lia).
    unfold ASAN_GT in GT.
    assert (Hfrlo : FS + 36864 <= fr) by
      (rewrite Efr; unfold fs_frame, fs_B; cbn [Z.of_nat Pos.of_succ_nat]; change (2 ^ 20) with 1048576;
       change (2 ^ 2) with 4; lia).
    rewrite (rc_neq0_64 fr) by lia. cbn [negb]. cbv iota.
    assert (FLb : FS + 28672 <= fs_flag FS 2 jj < FS + 32768).
    { unfold fs_flag. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 15) with 32768. change (2 ^ (15 - 2)) with 8192.
      lia. }
    assert (SHb : shadow_addr fr + 32 <= Sp - 9136).
    { unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia. }
    assert (STW2 : stk rsegs m2 (Sp - 9136) Sp).
    { apply (fl_stk _ m0 m2 _ _ STW MU2 WM2). intros x Hx.
      destruct (Z_lt_le_dec x (CA - 208)) as [L|L]; [|destruct (Z_lt_le_dec x CA) as [L2|L2]].
      - left. cbn [outside]. unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat].
        repeat split; try exact I; lia.
      - right. apply (rd_of_stk _ _ _ ST2). lia.
      - left. cbn [outside]. unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat].
        repeat split; try exact I; lia. }
    assert (WMw : wmono rsegs m m2) by (apply (wmono_trans _ _ _ _ WM WM2)).
    assert (FR2 : rw_cells rsegs m2 (Sp + -104) cmSAVES).
    { apply (rw_cells_transport rsegs _ m0 m2 _ _ FR MU2 WM2).
      cbn [disjoint_from cells_size csize Nat.add cmSAVES].
      unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat].
      repeat split; right; first [ lia | (unfold shadow_addr, ASAN_K; Z.div_mod_to_equations; lia) ]. }
    assert (MUw : munch [(Sp - 9136, Sp); (fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
                         (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]
                        m m2).
    { apply (munch_trans _ m m0 m2).
      - eapply munch_weaken; [|exact MU]. intros x Hx. cbn [outside] in *.
        split; [exact (proj1 Hx) | exact I].
      - eapply munch_weaken; [|exact MU2]. intros x Hx. cbn [outside] in Hx. exact (proj2 Hx). }
    assert (RMw : rd_mono m m2).
    { apply (rd_mono_list _ m m2 MUw). repeat constructor; cbn [fst snd]; intros y Hy.
      - apply (rd_of_stk _ _ _ STW2). lia.
      - apply (rd_of_stk _ _ _ FQstk). unfold fs_hint in Hy. cbn [Z.of_nat Pos.of_succ_nat] in Hy. unfold FS_SIZE. lia.
      - apply (rd_of_stk _ _ _ FQstk). unfold FS_SIZE. lia.
      - apply (rd_of_stk _ _ _ STF). lia.
      - apply (rd_of_stk _ _ _ STF). lia.
      - apply (rd_of_bytes _ _ _ HSH). rewrite repeat_length, Z2Nat.id by lia. lia.
      - apply (rd_of_stk _ _ _ ST2). lia. }
    eapply (cm_header Q fr CA jj 1 m2); [exact K|].
    apply (cm_mk_inv fr CA jj 1 m2 [(Sp - 9136, Sp); (fs_hint FS 2, fs_hint FS 2 + 8);
                     (fs_flag FS 2 jj, fs_flag FS 2 jj + 1); (fr + 24, fr + 32); (fr + 248, fr + 256);
                     (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]).
    + right. split; [exact Hjj | split; [exact Efr | split; reflexivity]].
    + exact MUw.
    + exact WMw.
    + exact RMw.
    + exact MI2.
    + intros x Hx. unfold aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hwn & Hxs).
      unfold aXs in Hxs. apply fl_out_app_inv in Hxs. destruct Hxs as (Hfpw & Hws).
      cbn [outside] in Hws. destruct Hws as (Hws & _).
      cbn [outside]. split; [exact Hwn|]. split.
      { exact (out_in _ _ _ _ Hfpw (fpw3_in_hint FS 2 ltac:(cbn; tauto))). }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_flag FS 2 ltac:(cbn; tauto))).
        unfold fs_flag, fs_M in *. destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
        change (2 ^ 12) with 4096 in *. destruct Hc. split; lia. }
      split.
      { intros Hc. apply (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))).
        rewrite Efr in *. unfold fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
        change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
        change (2 ^ 12) with 4096 in *. destruct Hc. split; lia. }
      split.
      { pose proof (out_in _ _ _ _ Hfpw (fpw3_in_shadow FS 2 ltac:(cbn; tauto))) as HFin.
        assert (GE : shadow_addr (fs_frame FS 2 0) <= shadow_addr fr).
        { apply acl_sh_ge. rewrite Efr. unfold fs_frame, fs_B. cbn [Z.of_nat Pos.of_succ_nat].
          change (2 ^ 20) with 1048576. lia. }
        assert (LE : shadow_addr fr + 32 <= shadow_addr (fs_frame FS 2 (fs_M 2))).
        { rewrite Efr. unfold shadow_addr, fs_frame, fs_B, fs_M in *. cbn [Z.of_nat Pos.of_succ_nat] in *.
          change (2 ^ 20) with 1048576 in *. change (2 ^ 2) with 4 in *. change (2 ^ (14 - 2)) with 4096 in *.
          change (2 ^ 12) with 4096 in *. Z.div_mod_to_equations; lia. }
        intros [A B]. clear -HFin GE LE A B. lia. }
      split; [|exact I].
      intros Hc. apply Hwn. clear -Hc CAlo CAhi. lia.
    + intros y Hy _.
      assert (Hap : app_mem y) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
      pose proof (rt_app_shadow y Hap) as Hsh.
      cbn [outside]. split.
      { unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hsh.
        clear -Hsh Hy HHM'. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_hint FS 2) (fs_hint FS 2 + 8) Hsh).
        intros z Hz. apply FSapp. unfold fs_hint in *. cbn [Z.of_nat Pos.of_succ_nat] in *. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fs_flag FS 2 jj) (fs_flag FS 2 jj + 1) Hsh).
        intros z Hz. apply FSapp. unfold FS_SIZE. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 24) (fr + 32) Hsh).
        intros z Hz. apply APF. lia. }
      split.
      { apply (sh_out_app (shadow_addr y) (fr + 248) (fr + 256) Hsh).
        intros z Hz. apply APF. lia. }
      split; [|split; [|exact I]].
      { intros [A B]. pose proof (acl_sh_ge y (fr + 8 * 32) ltac:(lia)) as G.
        rewrite (cm_sh_add8 fr 32 Hm8) in G. lia. }
      { apply (sh_out_app (shadow_addr y) (CA - 208) CA Hsh).
        intros z Hz. right. unfold HIGHMEM_BEG, APPMEM_END. clear -Hz Hy HHM' HAE' CAlo CAhi. lia. }
    + intros c Hc. cbn in Hc. destruct Hc as [Hc|[Hc|[Hc|[]]]]; subst c.
      * split.
        -- exists h0. apply (fl_bytes _ m _ (fs_hint FS 0) (le8 h0) HH0 MUw).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8.
        -- exists flags0. split; [|split; [exact HFl0 | exact HFb0]].
           apply (fl_bytes _ m _ (fs_flag FS 0 0) flags0 HF0 MUw).
           intros x Hx. rewrite HFl0 in Hx.
           cm_hdr_out FSapp Hm8.
      * split.
        -- exists h1. apply (fl_bytes _ m _ (fs_hint FS 1) (le8 h1) HH1 MUw).
           intros x Hx. rewrite length_le8 in Hx. cbn [Z.of_nat] in Hx.
           cm_hdr_out FSapp Hm8.
        -- exists flags1. split; [|split; [exact HFl1 | exact HFb1]].
           apply (fl_bytes _ m _ (fs_flag FS 1 0) flags1 HF1 MUw).
           intros x Hx. rewrite HFl1 in Hx.
           cm_hdr_out FSapp Hm8.
      * split.
        -- exists h2. exact HH2'.
        -- apply (cm_flag_upd m0 m2
             [(fs_hint FS 2, fs_hint FS 2 + 8); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1);
              (fr + 24, fr + 32); (fr + 248, fr + 256); (shadow_addr fr, shadow_addr fr + 32); (CA - 208, CA)]
             flags jj Hjj HFl2 HFb2 HF2 MU2); [| exact HFL].
           intros x Hx Hxne.
           assert (Hxap : app_mem x) by (apply FSapp; unfold fs_flag, fs_M in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
             change (2 ^ 15) with 32768 in *; change (2 ^ (15 - 2)) with 8192 in *;
             change (2 ^ (14 - 2)) with 4096 in *; change (2 ^ 12) with 4096 in *; unfold FS_SIZE; lia).
           assert (FL0 : fs_flag FS 2 0 = FS + 28672).
           { unfold fs_flag. cbn [Z.of_nat Pos.of_succ_nat]. change (2 ^ 15) with 32768.
             change (2 ^ (15 - 2)) with 8192. lia. }
           assert (FLj : fs_flag FS 2 jj = FS + 28672 + jj) by (unfold fs_flag in *; lia).
           change (fs_M 2) with 4096 in Hx.
           cbn [outside]. split.
           { unfold fs_hint. cbn [Z.of_nat Pos.of_succ_nat]. lia. }
           split.
           { intros [A B]. apply Hxne. lia. }
           split; [lia|].
           split; [lia|].
           split; [|split; [|exact I]].
           { intros [A B]. pose proof (acl_sh_out x fr (fr + 8 * 32) Hxap ltac:(lia) ltac:(unfold APPMEM_END; lia))
               as Hso.
             rewrite (cm_sh_add8 fr 32 Hm8) in Hso. apply Hso. split; [exact A | exact B]. }
           { lia. }
    + apply (cm_stk_sub _ fr (fr + 256)); [exact STF | lia | lia].
    + exact FR2.
    + intros _. exact Hflagword.
Qed.

(* The entry run from 0x84e40 to the join 0x84ee4: the 128-byte frame with the 13 saves at [Sp - 104, Sp), the
   aligned frame pointer CA, the loads of ASAN_K and of the flag word 1 through the runtime's cells, the class-2 frame
   request; then either the side-stack frame fs_frame FS 2 jj (body sp = CA) or, when every class-2 frame is in use,
   the page probe at CA - 4096 and the real-stack frame CA - 192 (body sp = CA - 192). Both arms build cmInv
   (cm_mk_inv) and continue through the header (cm_header) to the gate.  Composed of cm_pre_sm2, the class-2 request
   (asan_stack_malloc_2_contract_F_on, HSM2) and cm_post_sm2_real / cm_post_sm2_side. *)
Lemma cm_entry : forall (Q : machine_state -> Prop) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  cmKB Q ->
  evtF rsegs RNG Q
    (MS (mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None m (seg_rom rsegs)).
Proof.
  intros Q t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 K.
  eapply evtF_cut; [exact (cm_pre_sm2 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)|].
  intros ms (m0 & -> & HAt).
  pose proof HAt as (MU & WM & MI0 & STW & FR).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  pose proof (fl_fp [0%nat;1%nat;2%nat] m m0 (bv_unsigned tp) FS (Sp - 9136) Sp [] aDf
                [(Sp - 9136, Sp)] FP0 MU WM ltac:(intros x Hx; exact Hx)) as FP1.
  destruct FP1 as (DT & TS & C & T & DB & kk & HT1 & HTP1 & HPl1 & H881 & H961 & HCL1 & HFS1 & HAPP1 & HWd1 & HDd1).
  pose proof HCL1 as HCL1'. do 2 apply Forall_cons_iff in HCL1' as [_ HCL1']. apply Forall_cons_iff in HCL1' as [HC2 _].
  destruct HC2 as (_ & h & flags & HH2 & HF2 & HFl2 & HFb2).
  pose proof HWd1 as Hw0. unfold fp_dj in Hw0. apply Forall_cons_iff in Hw0. destruct Hw0 as [Hw0 _].
  cbn [fp_tls app] in Hw0.
  repeat (let Hd := fresh "Hd" in apply Forall_cons_iff in Hw0; destruct Hw0 as [Hd Hw0]; cbn [fst snd] in Hd).
  assert (AC0 : asan_cells m0).
  { apply (fl_asan_cells [(Sp - 9136, Sp)] m m0 AC MU). intros x Hx. unfold RT_LO, RT_HI in Hx.
    cbn [outside]. split; [clear -Hx HHM'; lia | exact I]. }
  pose proof (B.ShadowRwOnK.fl_shadow_rw_on _ [(Sp - 9136, Sp)] m m0
                (shadow_rw_on_mono cmR (asan_stack_malloc_shadow_R FS 2) m (cmOn_R_malloc f len Sp FS) SRo) MU WM
                (fun x Hx => fl_shadow_out _ (Sp - 9136) Sp x (fun y Hy => Hy) HHM Hx)) as SR0.
  pose proof (cm_stk_sub m0 (Sp - 9136) Sp (Sp - 9136) CA STW ltac:(lia) ltac:(lia)) as STA.
  pose proof HSM2 as HM. unfold asan_stack_malloc_2_contract_F_on, asan_stack_malloc_contract_F_on in HM.
  cbv zeta in HM.
  specialize (HM (proj1 (Nat.leb_le 2 10) eq_refl)).
  pose proof (cm_tls_rng m0 [(Sp - 9136, Sp)] MU
                ltac:(intros x Hx; unfold aWc in Hx; cbn [outside] in Hx |- *; split; [exact (proj1 Hx) | exact I])
                DT TS C T DB kk HT1) as RT1.
  destruct (tls_rngs RNG _ _ _ _ _ _ _ RT1) as (RTP8 & RDT & RTP88 & RTS & RC152 & RT48 & RDB).
  pose proof (rf_area 2 ltac:(cbn; tauto)) as (RA2 & RA2s).
  eapply evtF_cut.
  { eapply HM with (RNG := RNG) (lo := Sp - 9136) (FS := FS) (h := h) (DT := DT) (TS := TS) (C := C) (T := T)
      (DB := DB) (k := kk) (flags := flags).
    all: rewrite ?(unsigned_lit CA), ?(unsigned_lit 192) by lia.
    - unfold fs_B; cbn; lia.
    - reflexivity.
    - exact AC0.
    - exact SR0.
    - exact MI0.
    - exact HT1.
    - intros Hc; lia.
    - exact HTP1.
    - exact HPl1.
    - exact H881.
    - exact H961.
    - exact HH2.
    - exact HF2.
    - exact HFl2.
    - exact HFb2.
    - exact STA.
    - unfold ASAN_STACK_MALLOC_K; lia.
    - unfold ASAN_STACK_MALLOC_K; clear -HFS1 CAlo CAhi; lia.
    - intros a Ha; apply HAPP1; unfold ASAN_STACK_MALLOC_K in Ha; clear -Ha CAlo CAhi; lia.
    - cbn [disjoint_from]; unfold ASAN_STACK_MALLOC_K; repeat split; try exact I;
        match goal with |- _ + _ <= ?lo \/ ?hi <= _ =>
          match goal with Hd : ly_dj _ _ lo hi |- _ => unfold ly_dj in Hd; lia end end.
    - apply (rng_sub RNG _ _ _ _ RIMG); unfold IMG_LO, IMG_HI; lia.
    - apply (rng_sub RNG _ _ _ _ RWIN); unfold ASAN_STACK_MALLOC_K; lia.
    - exact RDT.
    - exact RTS.
    - exact RC152.
    - exact RT48.
    - exact RDB.
    - exact RHDR.
    - exact RA2.
    - exact RA2s.
    - exact RTP88.
    - exact RTP8. }
  intros ms' PO.
  destruct PO as (u0 & u1 & u2 & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & u3 & u4 & u5 & u6 & m2 & E &
                  WM2 & MI2 & ST2 & FSP2 & HH2' & ALT).
  rewrite (unsigned_lit CA) in ST2 by lia.
  destruct FSP2 as (_ & _ & _ & _ & FQstk).
  destruct ALT as [(_ & Ex0 & MUf) | (ii & Hii0 & _ & _ & FRM)].
  - (* the real-stack arm *)
    subst ms'. rewrite (unsigned_lit CA) in MUf by lia.
    exact (cm_post_sm2_real Q m0 m2 u0 u1 u2 x0 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 K HAt WM2 MI2 ST2 FQstk HH2'
             Ex0 MUf).
  - (* the side arm: exactly cm_fs_post_2 *)
    apply (cm_post_sm2_side Q m0 ms' K HAt).
    exists u0, u1, u2, x0, x1, x2, x3, x4, x5, x6, x7, u3, u4, u5, u6, m2.
    split; [exact E|]. split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact FQstk|].
    split; [exact HH2'|].
    exists ((bv_unsigned h + ii) mod fs_M 2). split; [apply Z.mod_pos_bound; reflexivity|].
    unfold asan_stack_malloc_frame in FRM. cbv zeta in FRM.
    rewrite (unsigned_lit CA), (unsigned_lit 192) in FRM by lia.
    replace (fs_B 2) with 256 in FRM by reflexivity.
    replace (fs_shadow_n 2 192) with 32 in FRM by reflexivity.
    destruct FRM as (Ex0' & Hm64' & _ & HFL' & _ & Hflagword' & HSH' & _ & STF' & APF' & FSlo' & FShi'' & GT' & FRA''
                     & DIS' & MU2').
    split; [exact Ex0'|]. split; [exact Hm64'|]. split; [exact HFL'|]. split; [exact Hflagword'|].
    split; [exact HSH'|]. split; [exact STF'|]. split; [exact APF'|]. split; [exact FSlo'|].
    split; [exact FShi''|]. split; [exact GT'|]. split; [exact FRA''|]. split; [exact DIS'|]. exact MU2'.
Qed.

(* ============================ the body: tail, row loop, gate and parse call ============================ *)

(* The shadow bytes of the frame at the current memory: a run of single-byte stores at shadow_addr fr + k (k < 24)
   writes only cmHF fr. cm_sh_begin sets up the facts the stores need (cm_wst, store_done); cm_sh_rd gives rd_mono for
   cm_inv_step at the end. *)
Ltac cm_sh_begin INVk :=
  let INV := fresh "INV" in
  pose proof INVk as INV;
  let FK := fresh "FK" in let WMg := fresh "WMg" in let MIg := fresh "MIg" in let SRg := fresh "SRg" in
  let STWg := fresh "STWg" in let STFg := fresh "STFg" in
  destruct INV as (FK & _ & WMg & MIg & (_ & SRg & _ & _) & _ & _ & STWg & STFg & _ & _);
  let FR32 := fresh "FR32" in let FRpos := fresh "FRpos" in let FR192 := fresh "FR192" in
  let FW := fresh "FW" in let FAP := fresh "FAP" in let FSW := fresh "FSW" in let FSPc := fresh "FSPc" in
  lazymatch type of FK with cmFK ?fr ?sp2 ?jj ?nn =>
    pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSPc);
    let RFR := fresh "RFR" in let RFS := fresh "RFS" in
    pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & _);
    let FR8 := fresh "FR8" in
    assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia);
    let SHIN := fresh "SHIN" in
    assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (shadow_addr fr + k))
      by (intros k Hk; rewrite <- (cm_sh_add8 fr k FR8); apply rt_app_shadow; apply FAP; lia);
    let SHlo := fresh "SHlo" in let SHhi := fresh "SHhi" in
    assert (SHlo : 0 <= shadow_addr fr) by (pose proof (rt_shadow_bound _ (SHIN 0 ltac:(lia))); lia);
    assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64) by (pose proof (rt_shadow_bound _ (SHIN 23 ltac:(lia))); lia);
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mc _) =>
      let STSH := fresh "STSH" in
      assert (STSH : stk rsegs mc (shadow_addr fr) (shadow_addr fr + 24))
        by (split; [lia|]; split; [lia|]; intros a Ha;
            replace a with (shadow_addr fr + (a - shadow_addr fr)) by lia;
            apply (cm_srw_fr fr sp2 jj nn mc _ FK SRg); [lia | apply SHIN; lia]);
      clear SRg;
      let MUh := fresh "MUh" in let WMh := fresh "WMh" in
      assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl;
      assert (WMh : wmono rsegs mc mc) by apply wmono_refl;
      unfold cmHF in MUh
    end
  end.

Ltac cm_sh_rd :=
  lazymatch goal with
  | MUh : munch _ ?mc ?mf, STWg : stk rsegs ?mf (Sp - 9136) Sp, STFg : stk rsegs ?mf ?fr (?fr + 192),
    STSH : stk rsegs ?mf (shadow_addr ?fr) (shadow_addr ?fr + 24) |- _ =>
      apply (rd_mono_list _ mc mf MUh); repeat constructor; cbn [fst snd]; intros y Hy;
      [ apply (rd_of_stk _ _ _ STWg); pose proof CA_facts; lia
      | apply (rd_of_stk _ _ _ STFg); lia
      | apply (rd_of_stk _ _ _ STSH); lia ]
  end.

(* The tail 0x850dc as a cut that ends at the exit state: the five shadow bytes 4..8 of the frame (the parse buffer)
   are set to 0xf8, and the run reaches 0x850fc in the state cm_exit_at, with s4 = r = want CM_T len fb. *)
Lemma cm_tail_K : forall fr sp2 jj nn mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG cm_exit_at
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850dc) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er INVk.
  cm_sh_begin INVk.
  step.
  cm_wst (shadow_addr fr + 4) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 5) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 6) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 7) 1%nat. step. store_done.
  cm_wst (shadow_addr fr + 8) 1%nat. step. store_done.
  step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) => assert (RMh : rd_mono mc mf) by cm_sh_rd end.
  apply evtF_done.
  eapply (cm_exit_at_intro fr sp2 jj nn _ r); [exact Er|].
  eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RMh | exact MIg].
Qed.

(* (a) The tail 0x850dc: cm_tail_K to the exit state 0x850fc, then cm_exit_at_post (cm_exit) with
   s4 = r = want CM_T len fb. *)
Lemma cm_tail : forall fr sp2 jj nn mc r
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG cmPost
    (MS (mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850dc) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er INVk.
  eapply evtF_cut;
    [exact (cm_tail_K fr sp2 jj nn mc r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
              Er INVk)|].
  exact cm_exit_at_post.
Qed.

(* ============================ the callees' writes ============================ *)

Lemma out_incl : forall L L' x, incl L' L -> outside L x -> outside L' x.
Proof.
  intros L L' x. induction L' as [|[lo hi] L' IH]; intros Hi Ho; cbn [outside]; [exact I|].
  split.
  - apply (out_in L lo hi x Ho). apply Hi. left. reflexivity.
  - apply IH; [intros d Hd; apply Hi; right; exact Hd | exact Ho].
Qed.

(* The side stack's layout in numbers. *)
Ltac fs_num :=
  unfold fs_hint, fs_flag, fs_frame, fs_M, fs_B in *; cbn [Z.of_nat Pos.of_succ_nat] in *;
  repeat first [ change (2 ^ 15) with 32768 in * | change (2 ^ (15 - 0)) with 32768 in *
               | change (2 ^ (14 - 0)) with 16384 in * | change (2 ^ (15 - 1)) with 16384 in *
               | change (2 ^ (14 - 1)) with 8192 in * | change (2 ^ (15 - 2)) with 8192 in *
               | change (2 ^ (14 - 2)) with 4096 in * | change (2 ^ 14) with 16384 in *
               | change (2 ^ 13) with 8192 in * | change (2 ^ 12) with 4096 in *
               | change (2 ^ 20) with 1048576 in * | change (2 ^ 0) with 1 in * | change (2 ^ 1) with 2 in *
               | change (2 ^ 2) with 4 in * ];
  unfold FS_SIZE in *.

(* A shadow byte of an application range with an 8-aligned start is a shadow byte. *)
Lemma sh_rng_in : forall p q y, p mod 8 = 0 -> (forall z, p <= z < q -> app_mem z) ->
  shadow_addr p <= y < shadow_addr q -> in_shadow y.
Proof.
  intros p q y Hp Hap Hy.
  assert (E : shadow_addr (8 * (y - ASAN_K)) = y) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
  rewrite <- E. apply rt_app_shadow. apply Hap. unfold shadow_addr in Hy. Z.div_mod_to_equations. lia.
Qed.

(* The writes of a callee that runs at sp2 with the window [lo, sp2): the window, a part [fr + a, fr + b) of the
   frame (its out-buffer), the class-c side-stack bytes and the shadow of the window. *)
Definition cmCF (sp2 lo a b : Z) (c : nat) (fr : Z) : list ivl :=
  [(lo, sp2); (fr + a, fr + b)] ++ fp_w [c] FS ++ [(shadow_addr lo, shadow_addr sp2)].

(* An application byte apart from the hint, the flags and the frames of class c is apart from fp_w [c] FS. *)
Lemma fpwc_out : forall c x, (c <= 1)%nat -> app_mem x ->
  ~ (fs_hint FS c <= x < fs_hint FS c + 8) -> ~ (fs_flag FS c 0 <= x < fs_flag FS c 0 + fs_M c) ->
  ~ (fs_frame FS c 0 <= x < fs_frame FS c (fs_M c)) -> outside (fp_w [c] FS) x.
Proof.
  intros c x Hc Hap H1 H2 H3. destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. pose proof HK.
  cbn [fp_w flat_map fp_w1 app outside]. split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  split; [|exact I].
  apply acl_sh_out; [exact Hap | |]; destruct c as [|[|c]]; try lia; fs_num; unfold APPMEM_END in *; lia.
Qed.

Lemma cm_cf_out_app : forall fr sp2 lo a b c x, app_mem x -> ~ (lo <= x < sp2) -> ~ (fr + a <= x < fr + b) ->
  outside (fp_w [c] FS) x -> 0 <= lo -> sp2 <= APPMEM_END -> outside (cmCF sp2 lo a b c fr) x.
Proof.
  intros fr sp2 lo a b c x Hap H1 H2 H3 H4 H5. unfold cmCF. cbn [app outside].
  split; [exact H1|]. split; [exact H2|].
  apply fl_out_app; [exact H3|]. cbn [outside]. split; [|exact I]. apply acl_sh_out; assumption.
Qed.

Lemma cm_cf_out_sh : forall fr sp2 lo a b c y, (c <= 1)%nat -> lo mod 8 = 0 ->
  (forall z, fr + a <= z < fr + b -> app_mem z) -> (forall z, lo <= z < sp2 -> app_mem z) ->
  app_mem y -> ~ (lo <= y < sp2) -> outside (fp_w [c] FS) y -> outside (cmCF sp2 lo a b c fr) (shadow_addr y).
Proof.
  intros fr sp2 lo a b c y Hc Hlo8 Hfap Hwap Hap Hy Hfw.
  pose proof (rt_app_shadow y Hap) as Hsh.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold cmCF. cbn [app outside].
  split; [exact (sh_out_app _ lo sp2 Hsh Hwap)|].
  split; [exact (sh_out_app _ (fr + a) (fr + b) Hsh Hfap)|].
  apply fl_out_app.
  - cbn [fp_w flat_map fp_w1 app outside] in Hfw |- *.
    destruct Hfw as (H1 & H2 & H3 & H4 & _).
    split; [apply (sh_out_app _ _ _ Hsh); intros z Hz; apply FSapp; destruct c as [|[|c]]; try lia; fs_num; lia|].
    split; [apply (sh_out_app _ _ _ Hsh); intros z Hz; apply FSapp; destruct c as [|[|c]]; try lia; fs_num; lia|].
    split; [apply (sh_out_app _ _ _ Hsh); intros z Hz; apply FSapp; destruct c as [|[|c]]; try lia; fs_num; lia|].
    split; [|exact I]. apply acl_win_sh; [|exact H3].
    destruct c as [|[|c]]; try lia; fs_num; Z.div_mod_to_equations; lia.
  - cbn [outside]. split; [|exact I]. apply acl_win_sh; [exact Hlo8 | exact Hy].
Qed.

Lemma cm_cf_sub : forall fr sp2 jj nn lo a b c, cmFK fr sp2 jj nn -> (c <= 1)%nat -> Sp - 9136 <= lo <= sp2 ->
  0 <= a <= b -> b <= 192 -> sub_fp (cmCF sp2 lo a b c fr) aWc.
Proof.
  intros fr sp2 jj nn lo a b c FK Hc Hlo Hab Hb x Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & _ & FR192 & _ & _ & _ & FSP).
  unfold aWc in Hx. cbn [outside] in Hx. destruct Hx as (Hw & Hxs).
  unfold aXs in Hxs. apply fl_out_app_inv in Hxs. destruct Hxs as (Hfpw & Hws).
  cbn [outside] in Hws. destruct Hws as (Hws & _).
  unfold cmCF. cbn [app outside].
  split; [destruct FSP; lia|].
  split.
  { destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)].
    - lia.
    - pose proof (out_in _ _ _ _ Hfpw (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as HFin. subst fr. fs_num. lia. }
  apply fl_out_app.
  - apply (out_incl (fp_w [0%nat; 1%nat; 2%nat] FS)); [|exact Hfpw].
    apply fp_w_incl. destruct c as [|[|c]]; [cbn; tauto | cbn; tauto | lia].
  - cbn [outside]. split; [|exact I].
    pose proof (acl_sh_ge lo (Sp - 9136) ltac:(lia)). pose proof (acl_sh_ge Sp sp2 ltac:(destruct FSP; lia)). lia.
Qed.

(* The hint and the flags of another class c' are apart from the callee's writes. *)
Lemma cm_cf_hdr : forall fr sp2 jj nn lo a b c c' x, cmFK fr sp2 jj nn -> (c <= 1)%nat -> (c' <= 2)%nat -> c' <> c ->
  Sp - 9136 <= lo <= sp2 -> 0 <= a <= b -> b <= 192 ->
  (fs_hint FS c' <= x < fs_hint FS c' + 8 \/ fs_flag FS c' 0 <= x < fs_flag FS c' 0 + fs_M c') ->
  outside (cmCF sp2 lo a b c fr) x.
Proof.
  intros fr sp2 jj nn lo a b c c' x FK Hc Hc' Hne Hlo Hab Hb Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & _ & FR192 & _ & _ & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold APPMEM_END, HIGHMEM_BEG in *.
  assert (Xr : FS <= x < FS + 32768) by (destruct c' as [|[|[|c']]]; try lia; fs_num; lia).
  assert (FRlo : FS + 36864 <= fr).
  { destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; [unfold FS_SIZE in *; lia | subst fr; fs_num; lia]. }
  apply cm_cf_out_app.
  - apply FSapp. unfold FS_SIZE. lia.
  - unfold FS_SIZE in *. lia.
  - lia.
  - apply fpwc_out; [exact Hc | apply FSapp; unfold FS_SIZE; lia | | |];
      destruct c as [|[|c]]; try lia; destruct c' as [|[|[|c']]]; try lia; fs_num; lia.
  - lia.
  - unfold APPMEM_END. destruct FSP; lia.
Qed.

(* The flag word of a side-stack frame is apart from the callee's writes. *)
Lemma cm_cf_flag : forall fr sp2 jj nn lo a b c x, cmFK fr sp2 jj nn -> nn = 1 -> (c <= 1)%nat ->
  Sp - 9136 <= lo <= sp2 -> 0 <= a <= b -> b <= 192 -> fr + 248 <= x < fr + 256 -> outside (cmCF sp2 lo a b c fr) x.
Proof.
  intros fr sp2 jj nn lo a b c x FK Enn Hc Hlo Hab Hb Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. unfold APPMEM_END in *.
  destruct FK as [(Ef & Es & Ej & En) | (Hj & Ef & Es & En)]; [subst nn; discriminate Enn|].
  subst fr sp2.
  assert (Xr : FS <= x < FS + FS_SIZE) by (fs_num; lia).
  apply cm_cf_out_app.
  - apply FSapp. lia.
  - lia.
  - lia.
  - apply fpwc_out; [exact Hc | apply FSapp; lia | | |]; destruct c as [|[|c]]; try lia; fs_num; lia.
  - lia.
  - unfold APPMEM_END. lia.
Qed.

(* The 13 saves are apart from the callee's writes. *)
Lemma cm_cf_saves : forall fr sp2 jj nn lo a b c x, cmFK fr sp2 jj nn -> (c <= 1)%nat ->
  Sp - 9136 <= lo <= sp2 -> 0 <= a <= b -> b <= 192 -> Sp - 104 <= x < Sp -> outside (cmCF sp2 lo a b c fr) x.
Proof.
  intros fr sp2 jj nn lo a b c x FK Hc Hlo Hab Hb Hx.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & _ & FR192 & _ & _ & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold APPMEM_END, HIGHMEM_BEG in *.
  assert (Hap : app_mem x) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
  apply cm_cf_out_app; [exact Hap | destruct FSP; lia | lia | | lia | unfold APPMEM_END; destruct FSP; lia].
  apply (out_incl (fp_w [0%nat; 1%nat; 2%nat] FS));
    [apply fp_w_incl; destruct c as [|[|c]]; [cbn; tauto | cbn; tauto | lia] |].
  apply acl_out_fpw_hi; [lia | exact Hap].
Qed.

(* Every byte the callee may write reads back after it. *)
Lemma cm_cf_rd : forall fr sp2 lo a b c mc', (c <= 1)%nat -> lo mod 8 = 0 -> (forall z, lo <= z < sp2 -> app_mem z) ->
  stk rsegs mc' lo sp2 -> (forall x, fr + a <= x < fr + b -> exists bb, mrd rsegs mc' (wa x) = Some bb) ->
  stk rsegs mc' FS (FS + FS_SIZE) -> cmSRT mc' -> Sp - 9136 <= lo -> sp2 <= Sp ->
  Forall (fun r => forall y, fst r <= y < snd r -> exists b, mrd rsegs mc' (wa y) = Some b) (cmCF sp2 lo a b c fr).
Proof.
  intros fr sp2 lo a b c mc' Hc Hlo8 Hwap STl RDf STfs SRm Hwlo Hsp2.
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold cmCF. apply Forall_app. split.
  { constructor; [|constructor; [|constructor]]; cbn [fst snd]; intros y Hy.
    - exact (rd_of_stk _ _ _ STl y Hy).
    - exact (RDf y Hy). }
  apply Forall_app. split.
  - cbn [fp_w flat_map fp_w1 app].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; cbn [fst snd]; intros y Hy.
    + apply (rd_of_stk _ _ _ STfs). destruct c as [|[|c]]; try lia; fs_num; lia.
    + apply (rd_of_stk _ _ _ STfs). destruct c as [|[|c]]; try lia; fs_num; lia.
    + apply (rd_of_stk _ _ _ STfs). destruct c as [|[|c]]; try lia; fs_num; lia.
    + refine (proj2 (cmSRT_R mc' SRm y _ _)).
      * apply (cmOn_R_area f len Sp FS (fs_frame FS c 0) (fs_frame FS c (fs_M c))); [| |exact Hy];
          destruct c as [|[|c]]; try lia; fs_num; lia.
      * apply (sh_rng_in (fs_frame FS c 0) (fs_frame FS c (fs_M c))); [| |exact Hy];
          destruct c as [|[|c]]; try lia; fs_num;
          first [ Z.div_mod_to_equations; lia | intros z Hz; apply FSapp; lia ].
  - constructor; [|constructor]. cbn [fst snd]. intros y Hy.
    exact (proj2 (cmSRT_R mc' SRm y (cmOn_R_win f len Sp FS lo sp2 Hwlo Hsp2 y Hy) (sh_rng_in lo sp2 y Hlo8 Hwap Hy))).
Qed.

(* The invariant after a run that wrote only Wm inside aWc, given what the run cannot keep by itself: the class
   hint/flag bytes, the window addressable outside the frame, and the saves and the flag word apart from Wm. *)
Lemma cm_inv_gen : forall fr sp2 jj nn mc mc' Wm,
  cmInv fr sp2 jj nn mc ->
  munch Wm mc mc' -> wmono rsegs mc mc' -> rd_mono mc mc' -> mem_inv rsegs mc' -> sub_fp Wm aWc ->
  (forall c, In c [0%nat; 1%nat; 2%nat] ->
     (exists h', bytes_at rsegs mc' (fs_hint FS c) (le8 h')) /\
     (exists flags', bytes_at rsegs mc' (fs_flag FS c 0) flags' /\ Z.of_nat (length flags') = fs_M c /\
        Forall (fun bb => bb = Z_to_bv 8 0 \/ bb = Z_to_bv 8 1) flags')) ->
  AWX fr mc' ->
  (forall x, Sp - 104 <= x < Sp -> outside Wm x) ->
  (nn = 1 -> forall x, fr + 248 <= x < fr + 256 -> outside Wm x) ->
  cmInv fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' Wm INV MU WM RM MI' SUB HCLS AWX' SAV FLGo.
  destruct INV as (FK & MUmc & WMmc & MImc & (ACmc & SRmc & FPg & TLg) & AWXg & EXTg & STWg & STFg & SVg & FLg).
  pose proof FPg as FPpack.
  destruct FPg as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & HT0 & HTPle & HPl & H88 & H96 & HCL & HFSlo & HApphi & HWd & HDd).
  destruct HPl as (HP1 & HP2 & HP3 & HP4 & HPstk).
  split; [exact FK|].
  split; [exact (munch_trans aWc m mc mc' MUmc (munch_weaken Wm aWc mc mc' SUB MU))|].
  split; [exact (wmono_trans rsegs m mc mc' WMmc WM)|].
  split; [exact MI'|].
  split.
  { split; [exact (fl_asan_cells Wm mc mc' ACmc MU (fun x Hx => SUB x (cm_rt_out_Wc x Hx)))|].
    split; [exact (shadow_rw_mono mc mc' SRmc WM RM)|].
    split.
    { apply (fl_fp_free [0%nat; 1%nat; 2%nat] mc mc' (bv_unsigned tp) FS (Sp - 9136) Sp aWf aDf Wm
               FPpack TLg MU WM).
      - unfold aWf, aWc, aXs in *. cbn [app]. exact SUB.
      - intros x Hx. apply SUB. exact (cm_hdr_out_Wc x Hx).
      - intros x Hx. right. apply RM. exact (rd_of_stk mc FS (FS + FS_SIZE) HPstk x Hx).
      - exact HCLS. }
    intros DT TS C T DB kk HTcells'.
    assert (Hc : Forall (fun d => forall x, fst d <= x < snd d -> outside Wm x)
                   (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0)).
    { apply Forall_forall. intros [a b] Hin x Hx. apply SUB. unfold aWc. cbn [outside]. split.
      - pose proof (fl_dj_out aWf (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 ++ [(FS, fs_frame FS 0 0)]) a b x
                      HWd (in_or_app _ _ _ (or_introl Hin)) Hx) as Ho.
        unfold aWf in Ho. cbn [outside] in Ho. exact (proj1 Ho).
      - exact (fl_dj_out_r (fp_tls (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0) aXs a b x
                 (TLg DT0 TS0 C0 T0 DB0 kk0 HT0) Hin Hx). }
    destruct (fl_tls_same mc mc' Wm (bv_unsigned tp) DT0 TS0 C0 T0 DB0 kk0 DT TS C T DB kk HT0 HTcells' MU Hc)
      as (E1 & E2 & E3 & E4 & E5 & E6). subst DT0 TS0 C0 T0 DB0 kk0.
    exact (TLg DT TS C T DB kk HT0). }
  split; [exact AWX'|].
  split; [exact (cm_EXT_keep Wm mc mc' EXTg MU SUB)|].
  split; [exact (stk_mono mc mc' _ _ STWg WM RM)|].
  split; [exact (stk_mono mc mc' _ _ STFg WM RM)|].
  split.
  { apply (acl_rw Wm mc mc' (Sp + -104) cmSAVES SVg MU WM).
    intros x Hx. apply SAV. unfold cmSAVES in Hx. cbn [cells_size csize] in Hx. lia. }
  intros Enn.
  apply (fl_bytes Wm mc mc' (fr + 248) (le8 (Z_to_bv 64 (fs_flag FS 2 jj))) (FLg Enn) MU).
  intros x Hx. rewrite length_le8 in Hx. apply (FLGo Enn). lia.
Qed.

(* The invariant after a callee run at sp2 with the window [lo, sp2) that wrote inside cmCF sp2 lo a b c fr (c = 0 or
   1): its window reads back and is addressable, its frame part reads back, the side stack reads back, the shadow
   is readable and writable, and the class-c state is the callee's. *)
Lemma cm_call_inv : forall fr sp2 jj nn mc mc' Wm lo a b c,
  cmInv fr sp2 jj nn mc -> (c <= 1)%nat ->
  Sp - 9136 <= lo <= sp2 -> lo mod 8 = 0 -> 0 <= a <= b -> b <= 192 ->
  munch Wm mc mc' -> sub_fp Wm (cmCF sp2 lo a b c fr) -> wmono rsegs mc mc' -> mem_inv rsegs mc' ->
  stk rsegs mc' lo sp2 -> addressable mc' lo (sp2 - lo) ->
  (forall x, fr + a <= x < fr + b -> exists bb, mrd rsegs mc' (wa x) = Some bb) ->
  stk rsegs mc' FS (FS + FS_SIZE) -> cmSRT mc' -> fp_cls mc' FS c ->
  cmInv fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' Wm lo a b c INV Hc Hlo Hlo8 Hab Hb MU0 SUBW WM MI' STl ADl RDf STfs SRm CLc.
  pose proof (munch_weaken Wm (cmCF sp2 lo a b c fr) mc mc' SUBW MU0) as MU.
  pose proof INV as INVk.
  destruct INV as (FK & _ & _ & _ & (_ & _ & FPg & _) & AWXg & _).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & _ & FAP & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold APPMEM_END, HIGHMEM_BEG in HAE', HHM'.
  assert (Hwap : forall z, lo <= z < sp2 -> app_mem z)
    by (intros z Hz; right; unfold HIGHMEM_BEG, APPMEM_END; destruct FSP; lia).
  assert (RM : rd_mono mc mc')
    by (apply (rd_mono_list _ mc mc' MU);
        exact (cm_cf_rd fr sp2 lo a b c mc' Hc Hlo8 Hwap STl RDf STfs SRm (proj1 Hlo) ltac:(destruct FSP; lia))).
  apply (cm_inv_gen fr sp2 jj nn mc mc' (cmCF sp2 lo a b c fr) INVk MU WM RM MI'
           (cm_cf_sub fr sp2 jj nn lo a b c FK Hc Hlo Hab Hb)).
  - intros c' Hc'.
    destruct (Nat.eq_dec c' c) as [->|Hne].
    + destruct CLc as (_ & h & flags & HH & HFl & HL & HF01). split; [exists h; exact HH|].
      exists flags. split; [exact HFl|]. split; [exact HL | exact HF01].
    + assert (Hc'2 : (c' <= 2)%nat) by (cbn in Hc'; destruct Hc' as [<-|[<-|[<-|[]]]]; lia).
      destruct FPg as (DT0 & TS0 & C0 & T0 & DB0 & kk0 & _ & _ & _ & _ & _ & HCL & _).
      pose proof (proj1 (Forall_forall _ _) HCL c' Hc') as (_ & h & flags & HH & HFl & HL & HF01).
      split.
      * exists h. apply (fl_bytes _ mc mc' _ _ HH MU). intros x Hx. rewrite length_le8 in Hx.
        apply (cm_cf_hdr fr sp2 jj nn lo a b c c' x FK Hc Hc'2 Hne Hlo Hab Hb). left. cbn [Z.of_nat] in Hx. lia.
      * exists flags. split; [|split; [exact HL | exact HF01]].
        apply (fl_bytes _ mc mc' _ _ HFl MU). intros x Hx. rewrite HL in Hx.
        apply (cm_cf_hdr fr sp2 jj nn lo a b c c' x FK Hc Hc'2 Hne Hlo Hab Hb). right. exact Hx.
  - intros y Hyw Hyf.
    destruct (Z_lt_le_dec y lo) as [L1|L1]; [|destruct (Z_lt_le_dec y sp2) as [L2|L2]].
    3: idtac.
    + apply (addr_byte_keep _ mc mc' y (AWXg y Hyw Hyf) MU).
      assert (Hap : app_mem y) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
      apply (cm_cf_out_sh fr sp2 lo a b c y Hc Hlo8); [intros z Hz; replace z with (fr + (z - fr)) by lia; apply FAP; lia
        | exact Hwap | exact Hap | lia |].
      apply (out_incl (fp_w [0%nat; 1%nat; 2%nat] FS));
        [apply fp_w_incl; destruct c as [|[|c]]; [cbn; tauto | cbn; tauto | lia] |].
      apply acl_out_fpw_hi; [lia | exact Hap].
    + destruct ADl as (_ & _ & _ & ADl). replace y with (lo + (y - lo)) by lia. apply ADl. lia.
    + apply (addr_byte_keep _ mc mc' y (AWXg y Hyw Hyf) MU).
      assert (Hap : app_mem y) by (right; unfold HIGHMEM_BEG, APPMEM_END; lia).
      apply (cm_cf_out_sh fr sp2 lo a b c y Hc Hlo8); [intros z Hz; replace z with (fr + (z - fr)) by lia; apply FAP; lia
        | exact Hwap | exact Hap | lia |].
      apply (out_incl (fp_w [0%nat; 1%nat; 2%nat] FS));
        [apply fp_w_incl; destruct c as [|[|c]]; [cbn; tauto | cbn; tauto | lia] |].
      apply acl_out_fpw_hi; [lia | exact Hap].
  - intros x Hx. exact (cm_cf_saves fr sp2 jj nn lo a b c x FK Hc Hlo Hab Hb Hx).
  - intros Enn x Hx. exact (cm_cf_flag fr sp2 jj nn lo a b c x FK Enn Hc Hlo Hab Hb Hx).
Qed.

(* ============================ the callees' premises ============================ *)

(* A callee window [lo, sp2) is addressable: it is in the window and below the frame (or the frame is on the side
   stack). *)
Lemma cm_awx_addr : forall fr sp2 jj nn mc lo n, cmInv fr sp2 jj nn mc -> Sp - 9136 <= lo -> 0 <= n ->
  lo + n <= sp2 -> addressable mc lo n.
Proof.
  intros fr sp2 jj nn mc lo n INV Hlo Hn Hhi.
  destruct INV as (FK & _ & _ & _ & _ & AWXg & _).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & _ & FR192 & _ & _ & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold APPMEM_END, HIGHMEM_BEG in *.
  split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; destruct FSP; lia|].
  intros i Hi. apply AWXg; [destruct FSP; lia|].
  destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)]; [lia|].
  subst fr. fs_num. lia.
Qed.

(* The thread cells are apart from the class-c bytes and the shadow of a callee window inside the window. *)
Lemma cm_tls_callee : forall mc c lo hi, (c <= 2)%nat -> aTL mc -> Sp - 9136 <= lo -> lo <= hi -> hi <= Sp ->
  forall DT TS C T DB k, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB k ->
  fp_dj (fp_tls (bv_unsigned tp) DT TS C T DB k) (fp_w [c] FS ++ [(shadow_addr lo, shadow_addr hi)]).
Proof.
  intros mc c lo hi Hc HTL H1 H2 H3 DT TS C T DB k HT.
  pose proof (HTL DT TS C T DB k HT) as D. unfold aXs in D. unfold fp_dj in *.
  pose proof (acl_sh_ge lo (Sp - 9136) H1) as G1. pose proof (acl_sh_ge Sp hi H3) as G2.
  pose proof (acl_sh_ge hi lo H2) as G3.
  eapply Forall_impl; [|exact D]. intros t Ht. cbn beta in Ht. apply Forall_app in Ht as [Ha Hb].
  apply Forall_app. split.
  - rewrite Forall_forall in Ha |- *. intros d Hd. apply Ha.
    apply (fp_w_incl c [0%nat; 1%nat; 2%nat] FS); [destruct c as [|[|[|c]]]; cbn; tauto + lia | exact Hd].
  - apply Forall_cons_iff in Hb as [Hb _]. constructor; [|constructor]. unfold ly_dj in *. cbn [fst snd] in *. lia.
Qed.

(* The side-stack premise of a class-c callee at sp2 with the window [lo, sp2), the out-buffer [fr + a, fr + b) and
   the data ranges Dx. *)
Lemma cm_fp_callee : forall fr sp2 jj nn mc c lo a b Dx,
  cmInv fr sp2 jj nn mc -> (c <= 1)%nat -> Sp - 9136 <= lo <= sp2 -> 0 <= a <= b -> b <= 192 ->
  fp_dj Dx (fp_w [c] FS) ->
  fp [c] mc (bv_unsigned tp) FS lo sp2 ((lo, sp2) :: [(fr + a, fr + b)]) Dx.
Proof.
  intros fr sp2 jj nn mc c lo a b Dx INV Hc Hlo Hab Hb HD.
  destruct INV as (FK & _ & _ & _ & (_ & _ & FPg & TLg) & _).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & _ & FR192 & _ & _ & _ & FSP).
  pose proof (fp_single c [0%nat; 1%nat; 2%nat] mc (bv_unsigned tp) FS (Sp - 9136) Sp aWf aDf
                ltac:(destruct c as [|[|c]]; cbn; tauto + lia) FPg) as FPc.
  destruct FPc as (DT & TS & C & T & DB & k & HT & HTP & HP & H88 & H96 & HCL & HFS & HApp & HWd & HDd).
  exists DT, TS, C, T, DB, k.
  split; [exact HT|]. split; [exact HTP|]. split; [exact HP|]. split; [exact H88|]. split; [exact H96|].
  split; [exact HCL|]. split; [lia|]. split; [intros z Hz; apply HApp; destruct FSP; lia|].
  split; [|exact HD].
  apply fl_dj_cons. split.
  - unfold aWf in HWd. apply (fl_dj_sub (Sp - 9136) Sp); [exact HWd | lia | destruct FSP; lia | lia].
  - destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)].
    + unfold aWf in HWd. apply (fl_dj_sub (Sp - 9136) Sp); [exact HWd | lia | lia | lia].
    + pose proof (TLg DT TS C T DB k HT) as TL. unfold aXs in TL.
      pose proof (cm_dj_in _ _ (fs_frame FS 2 0) (fs_frame FS 2 (fs_M 2)) (fr + a) (fr + b) TL
                    ltac:(apply in_or_app; left; apply fpw3_in_frame; cbn; tauto)
                    ltac:(subst fr; fs_num; lia) ltac:(subst fr; fs_num; lia)) as DJ.
      constructor; [|constructor]. apply Forall_app. split; [exact DJ|].
      constructor; [|constructor]. unfold ly_dj. cbn [fst snd]. subst fr. fs_num. lia.
Qed.

(* ============================ the row loop ============================ *)

Lemma cm_gate_len : cm_gate len fb = true -> 50 <= len.
Proof.
  unfold cm_gate. intros H. repeat (apply andb_prop in H; destruct H as [H _]). apply Z.leb_le. exact H.
Qed.

Lemma cm_b1 : forall mc A v, bytes_at rsegs mc A [v] -> mrd rsegs mc (wa A) = Some v.
Proof.
  intros mc A v (_ & _ & H). pose proof (H 0%nat ltac:(cbn; lia)) as HH. cbn [nth_error Z.of_nat] in HH.
  rewrite Z.add_0_r in HH. exact HH.
Qed.

(* The 32 bytes at fr0 + 8 j are addressable when the four shadow bytes j .. j + 3 are 0. *)
Lemma cm_z4 : forall mc fr0 j, fr0 mod 8 = 0 -> 0 <= fr0 -> 0 <= j -> fr0 + 8 * j + 32 <= APPMEM_END ->
  (forall i, 0 <= i < 32 -> app_mem (fr0 + 8 * j + i)) ->
  bytes_at rsegs mc (shadow_addr fr0 + j) [Z_to_bv 8 0] ->
  bytes_at rsegs mc (shadow_addr fr0 + (j + 1)) [Z_to_bv 8 0] ->
  bytes_at rsegs mc (shadow_addr fr0 + (j + 2)) [Z_to_bv 8 0] ->
  bytes_at rsegs mc (shadow_addr fr0 + (j + 3)) [Z_to_bv 8 0] ->
  addressable mc (fr0 + 8 * j) 32.
Proof.
  intros mc fr0 j Hm Hfr Hj Hhi Hap B0 B1 B2 B3.
  pose proof (cm_b1 _ _ _ B0) as R0. pose proof (cm_b1 _ _ _ B1) as R1.
  pose proof (cm_b1 _ _ _ B2) as R2. pose proof (cm_b1 _ _ _ B3) as R3.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Hap; exact Hi|].
  exists (Z_to_bv 8 0). split; [|unfold shadow_ok; left; vm_compute; reflexivity].
  destruct (Z_lt_le_dec i 8) as [c0|c0];
    [| destruct (Z_lt_le_dec i 16) as [c1|c1]; [| destruct (Z_lt_le_dec i 24) as [c2|c2]]].
  - replace (shadow_addr (fr0 + 8 * j + i)) with (shadow_addr fr0 + j)
      by (unfold shadow_addr; Z.div_mod_to_equations; lia). exact R0.
  - replace (shadow_addr (fr0 + 8 * j + i)) with (shadow_addr fr0 + (j + 1))
      by (unfold shadow_addr; Z.div_mod_to_equations; lia). exact R1.
  - replace (shadow_addr (fr0 + 8 * j + i)) with (shadow_addr fr0 + (j + 2))
      by (unfold shadow_addr; Z.div_mod_to_equations; lia). exact R2.
  - replace (shadow_addr (fr0 + 8 * j + i)) with (shadow_addr fr0 + (j + 3))
      by (unfold shadow_addr; Z.div_mod_to_equations; lia). exact R3.
Qed.

(* After the un-poisoning stores (shadow bytes 4..8 -> 0,0,0,0,4), the parse buffer [fr0 + 32, fr0 + 68) is
   addressable: the four 0 bytes make 32 granules usable, the 0x04 byte the first 4 of the next granule. *)
Lemma cm_parse_addr : forall (mc0 : word -> option byte) (fr0 : Z),
  fr0 mod 8 = 0 -> 0 <= fr0 -> fr0 + 68 <= APPMEM_END ->
  (forall i, 0 <= i < 36 -> app_mem (fr0 + 32 + i)) ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 4) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 5) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 6) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 7) [Z_to_bv 8 0] ->
  bytes_at rsegs mc0 (shadow_addr fr0 + 8) [Z_to_bv 8 4] ->
  addressable mc0 (fr0 + 32) 36.
Proof.
  intros mc0 fr0 Hm Hfr Hhi Hap B4 B5 B6 B7 B8.
  pose proof (cm_b1 _ _ _ B4) as R4. pose proof (cm_b1 _ _ _ B5) as R5. pose proof (cm_b1 _ _ _ B6) as R6.
  pose proof (cm_b1 _ _ _ B7) as R7. pose proof (cm_b1 _ _ _ B8) as R8.
  split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. split; [apply Hap; exact Hi|].
  destruct (Z_lt_le_dec i 8) as [c0|c0];
    [| destruct (Z_lt_le_dec i 16) as [c1|c1];
       [| destruct (Z_lt_le_dec i 24) as [c2|c2]; [| destruct (Z_lt_le_dec i 32) as [c3|c3]]]].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 4)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R4
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 5)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R5
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 6)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R6
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 0). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 7)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R7
      | unfold shadow_ok; left; vm_compute; reflexivity ].
  - exists (Z_to_bv 8 4). split;
      [ replace (shadow_addr (fr0 + 32 + i)) with (shadow_addr fr0 + 8)
          by (unfold shadow_addr; Z.div_mod_to_equations; lia); exact R8
      | unfold shadow_ok; right; change (bv_signed (Z_to_bv 8 4)) with 4;
        split; [ Z.div_mod_to_equations; lia | lia ] ].
Qed.

(* What a block of single-byte shadow stores needs (cm_wst, store_done) and gives back (cm_inv_step). *)
Lemma cm_shst_pre : forall fr sp2 jj nn mc, cmInv fr sp2 jj nn mc ->
  fr mod 8 = 0 /\ 0 < fr /\ fr + 192 <= CA /\ (forall i, 0 <= i < 192 -> app_mem (fr + i)) /\
  (forall i, 0 <= i < 24 -> wview rsegs m (wa (shadow_addr fr + i)) <> None) /\
  0 <= shadow_addr fr /\ shadow_addr fr + 24 <= 2 ^ 64 /\ wmono rsegs m mc /\ mem_inv rsegs mc /\
  stk rsegs mc (Sp - 9136) Sp /\ stk rsegs mc fr (fr + 192) /\
  stk rsegs mc (shadow_addr fr) (shadow_addr fr + 24).
Proof.
  intros fr sp2 jj nn mc (FK & _ & WMg & MIg & (_ & SRg & _ & _) & _ & _ & STWg & STFg & _ & _).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & _).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  assert (SHIN : forall k, 0 <= k < 24 -> in_shadow (shadow_addr fr + k))
    by (intros k Hk; rewrite <- (cm_sh_add8 fr k FR8); apply rt_app_shadow; apply FAP; lia).
  assert (SHlo : 0 <= shadow_addr fr) by (pose proof (rt_shadow_bound _ (SHIN 0 ltac:(lia))); lia).
  assert (SHhi : shadow_addr fr + 24 <= 2 ^ 64) by (pose proof (rt_shadow_bound _ (SHIN 23 ltac:(lia))); lia).
  split; [exact FR8|]. split; [exact FRpos|]. split; [exact FR192|]. split; [exact FAP|]. split; [exact FSW|].
  split; [exact SHlo|]. split; [exact SHhi|]. split; [exact WMg|]. split; [exact MIg|].
  split; [exact STWg|]. split; [exact STFg|].
  split; [lia|]. split; [lia|]. intros a Ha.
  replace a with (shadow_addr fr + (a - shadow_addr fr)) by lia.
  apply (cm_srw_fr fr sp2 jj nn mc _ FK SRg); [lia | apply SHIN; lia].
Qed.

(* After a 1-byte store at E (pc already past it): keep the stored byte as a bytes_at fact HB on the written memory
   (store_done's remember renames that memory in HB too), then store_done. *)
Ltac cm_keep HB :=
  lazymatch goal with
  | |- evtF ?segs ?RG ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem ?mm ?a ?bs) ?ro) =>
      let E := addr_expr a in
      change (write_to_mem mm a bs) with (write_to_mem mm (wa E) bs);
      assert (HB : bytes_at segs (write_to_mem mm (wa E) bs) E bs)
        by (apply bytes_at_write_same; simpl_sizes; lia);
      store_done
  end.

Ltac cm_rdm MU STW STF STS :=
  apply (rd_mono_list _ _ _ MU); repeat constructor; cbn [fst snd]; intros y Hy;
  [ apply (rd_of_stk _ _ _ STW); pose proof CA_facts; lia
  | apply (rd_of_stk _ _ _ STF); lia
  | apply (rd_of_stk _ _ _ STS); lia ].

(* A callee that writes only its window [lo, sp2) keeps the invariant. *)
Lemma cm_win_inv : forall fr sp2 jj nn mc mc' lo,
  cmInv fr sp2 jj nn mc -> Sp - 9136 <= lo <= sp2 -> lo mod 8 = 0 ->
  munch [(lo, sp2)] mc mc' -> wmono rsegs mc mc' -> mem_inv rsegs mc' ->
  stk rsegs mc' lo sp2 -> cmSRT mc' -> cmInv fr sp2 jj nn mc'.
Proof.
  intros fr sp2 jj nn mc mc' lo INV Hlo Hlo8 MU WM MI' STl SRm.
  pose proof INV as INVk.
  destruct INV as (FK & _ & _ & _ & (_ & _ & FPg & _) & _).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (_ & _ & FR192 & _ & _ & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  pose proof HAE as HAE'. pose proof HHM as HHM'. unfold APPMEM_END, HIGHMEM_BEG in HAE', HHM'.
  unfold FS_SIZE in FShi.
  pose proof FPg as FPc.
  destruct FPc as (DT & TS & C & T & DB & kk & _ & _ & HP & _ & _ & HCL & _).
  pose proof HP as (_ & _ & _ & _ & STfs).
  assert (DJfs : disjoint_from [(lo, sp2)] FS (FS + FS_SIZE - FS))
    by (cbn [disjoint_from]; split; [unfold FS_SIZE; lia | exact I]).
  assert (ADm : addressable mc lo (sp2 - lo))
    by exact (cm_awx_addr fr sp2 jj nn mc lo (sp2 - lo) INVk ltac:(lia) ltac:(lia) ltac:(lia)).
  apply (cm_call_inv fr sp2 jj nn mc mc' [(lo, sp2)] lo 0 0 0%nat INVk ltac:(lia) Hlo Hlo8 ltac:(lia) ltac:(lia)
           MU ltac:(intros x Hx; unfold cmCF in Hx; cbn [app outside] in Hx |- *;
                    split; [exact (proj1 Hx) | exact I]) WM MI' STl).
  - apply (acl_addr_munch [(lo, sp2)] mc mc' lo (sp2 - lo) ADm MU).
    intros i Hi. cbn [outside]. split; [|exact I].
    apply (sh_out_app _ lo sp2 (rt_app_shadow (lo + i) (acl_app_in mc lo (sp2 - lo) i ADm Hi))).
    intros z Hz. replace z with (lo + (z - lo)) by lia.
    exact (acl_app_in mc lo (sp2 - lo) (z - lo) ADm ltac:(lia)).
  - intros x Hx. lia.
  - exact (stk_transport_disjoint rsegs [(lo, sp2)] mc mc' FS (FS + FS_SIZE) STfs MU WM DJfs).
  - exact SRm.
  - apply Forall_cons_iff in HCL as [HC0 _].
    apply (fl_cls [(lo, sp2)] mc mc' FS 0%nat); [|exact MU|exact HC0].
    intros x Hx. cbn [outside]. split; [unfold FS_SIZE in *; lia | exact I].
Qed.

(* An application range and a shadow range are apart. *)
Lemma cm_dj_app_sh : forall a b u v, a < b -> u < v -> (forall z, a <= z < b -> app_mem z) ->
  (forall z, u <= z < v -> in_shadow z) -> ly_dj a b u v.
Proof.
  intros a b u v Hab Huv Hap Hsh. unfold ly_dj.
  destruct (Z_le_gt_dec b u) as [H|H]; [left; lia|].
  destruct (Z_le_gt_dec v a) as [H2|H2]; [right; lia|].
  exfalso. destruct (Z_le_gt_dec a u) as [Hau|Hau];
    [ exact (acl_app_not_shadow u (Hap u ltac:(lia)) (Hsh u ltac:(lia)))
    | exact (acl_app_not_shadow a (Hap a ltac:(lia)) (Hsh a ltac:(lia))) ].
Qed.

(* [a, b) below the side stack is apart from the class-c side-stack bytes. *)
Lemma cm_dj_lo : forall a b c, (c <= 1)%nat -> 0 <= a -> a < b -> b <= ASAN_GT -> fp_dj [(a, b)] (fp_w [c] FS).
Proof.
  intros a b c Hc Ha Hab Hb. destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  assert (HAP : forall z, a <= z < b -> app_mem z)
    by (intros z Hz; left; unfold ASAN_GT, LOWMEM_END in *; lia).
  unfold fp_dj. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  cbn [fp_w flat_map fp_w1 app].
  apply Forall_cons; [cbn [fst snd]; unfold ly_dj; destruct c as [|[|c]]; try lia; fs_num;
                      unfold ASAN_GT in *; lia|].
  apply Forall_cons; [cbn [fst snd]; unfold ly_dj; destruct c as [|[|c]]; try lia; fs_num;
                      unfold ASAN_GT in *; lia|].
  apply Forall_cons; [cbn [fst snd]; unfold ly_dj; destruct c as [|[|c]]; try lia; fs_num;
                      unfold ASAN_GT in *; lia|].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  apply (cm_dj_app_sh a b _ _ Hab); [| exact HAP |].
  - destruct c as [|[|c]]; try lia; fs_num; unfold shadow_addr; Z.div_mod_to_equations; lia.
  - intros z Hz. apply (sh_rng_in (fs_frame FS c 0) (fs_frame FS c (fs_M c)) z);
      [destruct c as [|[|c]]; try lia; fs_num; Z.div_mod_to_equations; lia
      | intros y Hy; apply FSapp; destruct c as [|[|c]]; try lia; fs_num; lia
      | exact Hz].
Qed.

(* A part of the frame is apart from the class-c side-stack bytes (c <= 1). *)
Lemma cm_dj_fr : forall fr sp2 jj nn a b c, cmFK fr sp2 jj nn -> (c <= 1)%nat -> 0 <= a -> a < b -> b <= 192 ->
  fp_dj [(fr + a, fr + b)] (fp_w [c] FS).
Proof.
  intros fr sp2 jj nn a b c FK Hc Ha Hab Hb.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & _ & FAP & _ & _).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & _).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt.
  assert (FRlo : FS + 36864 + 2097152 <= fr).
  { destruct FK as [(Ef & _ & _ & _) | (Hj & Ef & _ & _)]; [lia | subst fr; fs_num; lia]. }
  assert (HAP : forall z, fr + a <= z < fr + b -> app_mem z)
    by (intros z Hz; replace z with (fr + (z - fr)) by lia; apply FAP; lia).
  unfold fp_dj. apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  cbn [fp_w flat_map fp_w1 app].
  apply Forall_cons; [cbn [fst snd]; unfold ly_dj; destruct c as [|[|c]]; try lia; fs_num; lia|].
  apply Forall_cons; [cbn [fst snd]; unfold ly_dj; destruct c as [|[|c]]; try lia; fs_num; lia|].
  apply Forall_cons; [cbn [fst snd]; unfold ly_dj; destruct c as [|[|c]]; try lia; fs_num; lia|].
  apply Forall_cons; [|apply Forall_nil]. cbn [fst snd].
  apply (cm_dj_app_sh (fr + a) (fr + b) _ _ ltac:(lia)); [| exact HAP |].
  - destruct c as [|[|c]]; try lia; fs_num; unfold shadow_addr; Z.div_mod_to_equations; lia.
  - intros z Hz. apply (sh_rng_in (fs_frame FS c 0) (fs_frame FS c (fs_M c)) z);
      [destruct c as [|[|c]]; try lia; fs_num; Z.div_mod_to_equations; lia
      | intros y Hy; apply FSapp; destruct c as [|[|c]]; try lia; fs_num; lia
      | exact Hz].
Qed.

(* The state at the call of reac_box_model_block at 0x85098 (callee entry 0x865d8, return 0x8509c) for row i: the
   frame invariant at the call memory and the buffer [fr + 112, fr + 144) addressable. *)
Definition cmAtMB (i : nat) (fr sp2 jj nn : Z) (m0 : word -> option byte) : Prop :=
  (i < 11)%nat /\ cmInv fr sp2 jj nn m0 /\ addressable m0 (fr + 112) 32.

(* The post of reac_box_model_block_contract_F_on (reac_box_model_block_post_on of reac_box_model_block_c_on.v) at
   this call (p = CM_T + 296 i <> 0, b = 0, o = fr + 112 <> 0, row = cm_row i, nb = []), without its asan_cells and
   tls conjuncts, and of its fp [0%nat] conjunct only fs_place's stk conjunct and the class-0 clause. *)
Definition cm_mb_post (i : nat) (fr sp2 nn : Z) (w9 : word) (m0 : word -> option byte) (ms' : machine_state)
    : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                  (Z_to_bv 64 (rc (cm_row i) 0)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
                  (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9
                  (Z_to_bv 64 1) (Z_to_bv 64 (-8)) t3' t4' t5' t6')
             F (ret_pc (Z_to_bv 64 0x8509c)) fc None m' (seg_rom rsegs) /\
    bytes_at rsegs m' (fr + 112) (synth (cm_row i) 0 []) /\
    munch ([(sp2 - REAC_BOX_MODEL_BLOCK_K, sp2); (fr + 112, fr + 112 + 32)] ++ reac_box_model_block_X sp2 FS)
      m0 m' /\
    wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' (sp2 - REAC_BOX_MODEL_BLOCK_K) sp2 /\
    (forall P, shadow_rw_on P m0 -> shadow_rw_on P m') /\
    addressable m' (sp2 - REAC_BOX_MODEL_BLOCK_K) REAC_BOX_MODEL_BLOCK_K /\
    stk rsegs m' FS (FS + FS_SIZE) /\ fp_cls m' FS 0%nat.

(* The stretch from 0x8508c to the call of reac_box_model_block (a0 = the row, a1 = 0, a2 = the buffer fr + 112). *)
Lemma cm_pre_mb : forall (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (w4 w9 : word) (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (i < 11)%nat -> w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) ->
  cmInv fr sp2 jj nn mc -> addressable mc (fr + 112) 32 ->
  evtF rsegs RNG
    (fun ms => exists m0, ms =
       MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
               w4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
               (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
               (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x865d8) fc None m0 (seg_rom rsegs) /\ cmAtMB i fr sp2 jj nn m0)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x8508c) fc None mc (seg_rom rsegs)).
Proof.
  intros i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 Hi E4 INVk ADo.
  subst w4.
  do 4 step.
  apply evtF_done. cbv beta. exists mc. split; [reflexivity | exact (conj Hi (conj INVk ADo))].
Qed.

(* The turn's head 0x8507c as a cut that ends at the call of reac_box_model_block: the four shadow bytes 14..17 of
   the frame := 0 mark the 32-byte buffer at fr + 112 usable, then the stretch 0x8508c .. 0x85098 into the callee's
   entry 0x865d8 (cm_pre_mb), where cmAtMB i holds at the call memory. *)
Lemma cm_turn_head : forall (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte) (w4 w9 : word)
    (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  cm_gate len fb = true -> (i < 11)%nat -> w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) ->
  cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG
    (fun ms => exists m0, ms =
       MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
               w4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) ra3 ra4 ra5 ra6 ra7
               (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
               (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
               (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
          F (Z_to_bv 64 0x865d8) fc None m0 (seg_rom rsegs) /\ cmAtMB i fr sp2 jj nn m0)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x8507c) fc None mc (seg_rom rsegs)).
Proof.
  intros i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 G Hi E4 INVk.
  subst w4.
  pose proof INVk as (FKl & _). pose proof (cm_fr_rng fr sp2 jj nn FKl) as (RFR & RFS & _). clear FKl.
  pose proof (cm_gate_len G) as L.
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  (* the four shadow bytes 14..17 of the frame := 0 *)
  destruct (cm_shst_pre _ _ _ _ _ INVk)
    as (FR8 & FRpos & FR192 & FAP & FSWm & SHlo & SHhi & WMm & MIg & STWg & STFg & STSH).
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  unfold cmHF in MUh.
  cm_wst (shadow_addr fr + 14) 1%nat. step. cm_keep B14.
  cm_wst (shadow_addr fr + 15) 1%nat. step. cm_keep B15.
  cm_wst (shadow_addr fr + 16) 1%nat. step. cm_keep B16.
  cm_wst (shadow_addr fr + 17) 1%nat. step. cm_keep B17.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (RM1 : rd_mono mc mf) by (cm_rdm MUh STWg STFg STSH);
    assert (INV1 : cmInv fr sp2 jj nn mf)
      by (eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RM1 | exact MIg]);
    assert (AD1 : addressable mf (fr + 112) 32)
      by (replace (fr + 112) with (fr + 8 * 14) by lia;
          apply (cm_z4 mf fr 14 FR8 ltac:(lia) ltac:(lia) ltac:(unfold APPMEM_END; lia)
                   ltac:(intros ii Hii; replace (fr + 8 * 14 + ii) with (fr + (112 + ii)) by lia; apply FAP; lia));
          [exact B14 | exact B15 | exact B16 | exact B17])
  end.
  clear B14 B15 B16 B17 MUh WMh RM1.
  (* 0x8508c .. 0x85098: the stretch into the call of reac_box_model_block *)
  eapply cm_pre_mb; [exact Hi | reflexivity | exact INV1 | exact AD1].
Qed.

(* From the return of reac_box_model_block (0x8509c) to the continuation: the result is rc (cm_row i) 0 = 1, the
   buffer holds the row's declaration, and the invariant holds at the returned memory (cm_call_inv). *)
Lemma cm_post_mb : forall (Q : machine_state -> Prop) (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (w9 : word) (ms' : machine_state),
  cmAtMB i fr sp2 jj nn mc -> cm_mb_post i fr sp2 nn w9 mc ms' ->
  (forall (mc' : word -> option byte) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     cmInv fr sp2 jj nn mc' -> bytes_at rsegs mc' (fr + 112) (nth i DECLS []) ->
     addressable mc' (fr + 112) 32 ->
     evtF rsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                (Z_to_bv 64 1) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
                (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9
                (Z_to_bv 64 1) (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
           F (Z_to_bv 64 0x8509c) fc None mc' (seg_rom rsegs))) ->
  evtF rsegs RNG Q ms'.
Proof.
  intros Q i fr sp2 jj nn mc w9 ms' HAt PO K.
  destruct HAt as (Hi & INVk & ADo).
  pose proof INVk as INVc.
  destruct INVc as (FK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSP).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt, FRgt.
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  assert (Rsp2b : Sp - 336 <= sp2 <= Sp - 128) by (destruct FSP; lia).
  assert (Rlo : Sp - 9136 <= sp2 - 4272 <= sp2) by (destruct FSP; lia).
  assert (Lo8 : (sp2 - 4272) mod 8 = 0)
    by (destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia).
  assert (FRsp : fr + 256 <= sp2 - 4272 \/ sp2 <= fr)
    by (destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)]; [right; lia | left; subst fr sp2; fs_num; lia]).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                  BB & MUm & WMb & MIb & STb & SRb & ADb & STfsb & CL0).
  rewrite ret_pc_even by (try lia; reflexivity).
  destruct (cm_rc i (@nil byte) Hi) as [RC SY]. rewrite RC. rewrite SY in BB.
  unfold REAC_BOX_MODEL_BLOCK_K in MUm, STb, ADb.
  assert (MUc : munch (cmCF sp2 (sp2 - 4272) 112 144 0%nat fr) mc m').
  { unfold cmCF. unfold reac_box_model_block_X, REAC_BOX_MODEL_BLOCK_K in MUm.
    rewrite ?(unsigned_lit sp2) in MUm by lia.
    replace (fr + 112 + 32) with (fr + 144) in MUm by lia. exact MUm. }
  assert (INV' : cmInv fr sp2 jj nn m').
  { apply (cm_call_inv fr sp2 jj nn mc m' (cmCF sp2 (sp2 - 4272) 112 144 0%nat fr) (sp2 - 4272) 112 144 0%nat
             INVk ltac:(lia) Rlo Lo8 ltac:(lia) ltac:(lia) MUc ltac:(intros x Hx; exact Hx) WMb MIb STb).
    - replace (sp2 - (sp2 - 4272)) with 4272 by lia. exact ADb.
    - intros x Hx. apply (rd_of_bytes m' (fr + 112) (nth i DECLS []) BB).
      rewrite (cm_decl_len i Hi). cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - exact STfsb.
    - exact (cmSRT_step mc m' (cm_inv_srt fr sp2 jj nn mc INVk) SRb).
    - exact CL0. }
  apply K; [exact INV' | exact BB |].
  apply (acl_addr_munch (cmCF sp2 (sp2 - 4272) 112 144 0%nat fr) mc m' (fr + 112) 32 ADo MUc).
  intros ii Hii.
  apply (cm_cf_out_sh fr sp2 (sp2 - 4272) 112 144 0%nat (fr + 112 + ii) ltac:(lia) Lo8).
  - intros z Hz. replace z with (fr + (z - fr)) by lia. apply FAP. lia.
  - intros z Hz. right. unfold HIGHMEM_BEG, APPMEM_END. destruct FSP; lia.
  - replace (fr + 112 + ii) with (fr + (112 + ii)) by lia. apply FAP. lia.
  - destruct FRsp; lia.
  - exact (fl_dj_out_r [(fr + 112, fr + 144)] (fp_w [0%nat] FS) (fr + 112) (fr + 144) (fr + 112 + ii)
             (cm_dj_fr fr sp2 jj nn 112 144 0%nat FK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
             ltac:(left; reflexivity) ltac:(lia)).
Qed.

(* The call of reac_box_model_block, from the callee's entry 0x865d8 (a0 = the row, a1 = 0, a2 = the 32-byte buffer
   fr + 112) to the return 0x8509c: its result is rc (cm_row i) 0 = 1 and the buffer holds the row's declaration.
   Composed of the call (reac_box_model_block_contract_F_on) and cm_post_mb; the stretch into the call is
   cm_turn_head, which ends in this state. *)
Lemma cm_mb : forall (Q : machine_state -> Prop) (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (w4 w9 : word) (rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  50 <= len -> w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> cmAtMB i fr sp2 jj nn mc ->
  (forall (mc' : word -> option byte) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     cmInv fr sp2 jj nn mc' -> bytes_at rsegs mc' (fr + 112) (nth i DECLS []) ->
     addressable mc' (fr + 112) 32 ->
     evtF rsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                (Z_to_bv 64 1) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
                (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
                (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
           F (Z_to_bv 64 0x8509c) fc None mc' (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             w4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x865d8) fc None mc (seg_rom rsegs)).
Proof.
  intros Q i fr sp2 jj nn mc w4 w9 rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 L E4 HAt K.
  pose proof HAt as (Hi & INVk & ADo).
  subst w4.
  pose proof INVk as INVc.
  destruct INVc as (FK & _ & _ & MIg & (ACg & SRg & FPg & TLg) & AWXg & EXTg & STWg & STFg & _ & _).
  destruct EXTg as (EF & EAT & EBT & EBC & ECL).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSP).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & RFC).
  assert (TLR : forall DT TS C T DB kk, asan_tls_cells mc (bv_unsigned tp) DT TS C T DB kk ->
            Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB kk))
    by (destruct INVk as (_ & MUa & _); exact (cm_tls_rng mc aWc MUa (fun x Hx => Hx))).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt, FRgt.
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  assert (Rsp2b : Sp - 336 <= sp2 <= Sp - 128) by (destruct FSP; lia).
  assert (Rlo : Sp - 9136 <= sp2 - 4272 <= sp2) by (destruct FSP; lia).
  assert (Lo8 : (sp2 - 4272) mod 8 = 0)
    by (destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia).
  assert (FRsp : fr + 256 <= sp2 - 4272 \/ sp2 <= fr)
    by (destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)]; [right; lia | left; subst fr sp2; fs_num; lia]).
  pose proof (bytes_at_sub rsegs mc CM_T CM_TBL (296 * i) 296 EBT ltac:(rewrite CM_TBL_len; lia)) as BR.
  apply (bytes_at_addr rsegs mc _ (CM_T + 296 * Z.of_nat i)) in BR; [|lia].
  fold (cm_row i) in BR.
  destruct (cm_rw_stk mc fr (fr + 192) (fr + 112) 32 STFg ltac:(lia) ltac:(cbn; lia)) as (ob & RWo).
  eapply evtF_cut.
  { eapply HMB with (RNG := RNG) (p := CM_T + 296 * Z.of_nat i) (b := 0) (o := fr + 112) (row := cm_row i)
                    (nb := @nil byte) (ob := ob).
    all: try reflexivity.
    all: cbv zeta.
    all: rewrite ?unsigned_lit by lia.
    all: unfold REAC_BOX_MODEL_BLOCK_K.
    all: lazymatch goal with
         | |- stk _ _ _ _ => apply (cm_stk_sub mc (Sp - 9136) Sp); [exact STWg | lia | lia]
         | |- mem_inv _ _ => exact MIg
         | |- asan_cells _ => exact ACg
         | |- shadow_rw_on _ _ =>
             exact (shadow_rw_on_mono _ _ mc (cmOn_R_mb f len Sp FS fr sp2 jj nn i (cm_row i) [] L Hi FK)
                      (cmSRT_R mc SRg))
         | |- addressable _ _ 4272 =>
             exact (cm_awx_addr fr sp2 jj nn mc (sp2 - 4272) 4272 INVk ltac:(lia) ltac:(lia) ltac:(lia))
         | |- _ <> 0 -> (_ = 5 \/ _ = 6) -> _ => intros _ [Hb|Hb]; discriminate Hb
         | |- _ <> 0 -> _ mod 8 = 0 /\ _ =>
             intros _;
             split; [replace (CM_T + 296 * Z.of_nat i) with ((81604 + 37 * Z.of_nat i) * 8)
                       by (unfold CM_T; lia); apply Z_mod_mult|];
             split; [apply cm_row_len; exact Hi|];
             split; [exact BR|];
             split; [right; unfold CM_T; lia | right; right; unfold CM_T; lia]
         | |- _ <> 0 -> rw_cells _ _ _ _ /\ _ =>
             intros _; split; [exact RWo|];
             split; [destruct FRsp; [right; lia | left; lia] | right; unfold JOIN_0014; lia]
         | |- _ <> 0 -> addressable _ _ 296 =>
             intros _; exact (acl_addr_sub mc CM_T 3256 (CM_T + 296 * Z.of_nat i) 296 EAT
                                ltac:(lia) ltac:(lia) ltac:(unfold CM_T in *; lia))
         | |- _ <> 0 -> addressable _ _ 32 /\ _ =>
             intros _; split; [exact ADo|];
             split; [replace (fr + 112 + 32) with (fr + 144) by lia; apply FAP; lia
                    | right; unfold RT_HI; lia]
         | |- _ = 1 -> _ => intros Hb; discriminate Hb
         | |- _ = 2 -> _ => intros Hb; discriminate Hb
         | |- fp _ _ _ _ _ _ _ _ =>
             unfold reac_box_model_block_W, reac_box_model_block_D;
             replace (fr + 112 =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
             replace (CM_T + 296 * Z.of_nat i =? 0) with false by (symmetry; apply Z.eqb_neq; unfold CM_T; lia);
             cbn [app]; replace (fr + 112 + 32) with (fr + 144) by lia;
             apply (cm_fp_callee fr sp2 jj nn mc 0%nat (sp2 - 4272) 112 144 _ INVk ltac:(lia) Rlo
                      ltac:(lia) ltac:(lia));
             apply fl_dj_cons;
             split; [apply (cm_dj_lo _ _ 0%nat); [lia | unfold CM_T; lia | unfold CM_T; lia
                                                 | unfold CM_T, ASAN_GT; lia]|];
             apply fl_dj_cons;
             split; [exact (cm_dj_fr fr sp2 jj nn 112 144 0%nat FK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                    | constructor]
         | |- reac_box_model_block_tls _ _ _ _ _ =>
             exact (cm_tls_callee mc 0%nat (sp2 - 4272) sp2 ltac:(lia) TLg ltac:(lia) ltac:(lia) ltac:(lia))
         | |- RngBytes.rng_bytes _ => exact RB
         | |- rng _ _ _ => first [ exact RIMG | exact RHDR | apply (rng_sub RNG _ _ _ _ RWIN); lia ]
         | |- sh_cover _ _ _ => apply cm_win_shc; lia
         | |- Forall _ (fp_w _ _) => exact (rf_fpw_c 0%nat ltac:(cbn; tauto))
         | |- _ <> 0 -> _ <> 0 -> rng _ _ _ /\ sh_cover _ _ _ =>
             intros _ _; split; [apply (rng_sub RNG _ _ _ _ RFR); lia | apply RFC; lia]
         | |- _ <> 0 -> rng _ _ _ /\ sh_cover _ _ _ =>
             intros _; split; [apply (rng_sub RNG _ _ _ _ RTB); lia | apply RTW; lia]
         | |- _ => first [ exact TLR | unfold CM_T; lia ]
         end. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
              PB & WMb & MIb & STb & ACb & SRb & ADb & FPb & TLb).
  apply (cm_post_mb Q i fr sp2 jj nn mc w9 _ HAt); [|exact K].
  assert (Z0 : (CM_T + 296 * Z.of_nat i =? 0) || (fr + 112 =? 0) = false)
    by (apply orb_false_iff; split; apply Z.eqb_neq; unfold CM_T; lia).
  rewrite Z0 in PB. destruct PB as [BB MUm].
  rewrite ?(unsigned_lit sp2) in MUm, STb, ADb, FPb by lia.
  pose proof FPb as (DTb & TSb & Cb & Tb & DBb & kkb & _ & _ & HPb & _ & _ & HCLb & _).
  pose proof HPb as (_ & _ & _ & _ & STfsb).
  apply Forall_cons_iff in HCLb as [CL0 _].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  rewrite Z0. split; [reflexivity|].
  exact (conj BB (conj MUm (conj WMb (conj MIb (conj STb (conj SRb (conj ADb (conj STfsb CL0)))))))).
Qed.

(* The call of the bcmp wrapper at 0x850b4 on (f + 18, fr + 112, 32): its result is 0 exactly when the input's
   32 bytes are the row's declaration. *)
Lemma cm_bc : forall (Q : machine_state -> Prop) (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte)
    (w4 w9 : word) (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  (i < 11)%nat -> 50 <= len ->
  cmInv fr sp2 jj nn mc -> bytes_at rsegs mc (fr + 112) (nth i DECLS []) -> addressable mc (fr + 112) 32 ->
  (forall (mc' : word -> option byte) (v : Z) (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     cmInv fr sp2 jj nn mc' -> -256 < v < 256 -> (v = 0 <-> cm_blk fb = nth i DECLS []) ->
     evtF rsegs RNG Q
       (MS (mkR (Z_to_bv 64 0x850b8) (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                (Z_to_bv 64 v) ya1 ya2 ya3 ya4 ya5 ya6 ya7
                (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
                (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
                (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
           F (Z_to_bv 64 0x850b8) fc None mc' (seg_rom rsegs))) ->
  evtF rsegs RNG Q
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x850a8) fc None mc (seg_rom rsegs)).
Proof.
  intros Q i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
    Hi L INVk BB ADo K.
  pose proof INVk as INVc.
  destruct INVc as (FK & _ & _ & MIg & (ACg & SRg & FPg & TLg) & AWXg & EXTg & STWg & STFg & _ & _).
  destruct EXTg as (EF & EAT & EBT & EBC & ECL).
  destruct (EF L) as (BF & AF).
  destruct ECL as (C1 & C2 & C3 & C4 & C5).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  destruct (AFU L) as (_ & APf50).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & FW & FAP & FSW & FSP).
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt, FRgt.
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  assert (Rsp2b : Sp - 336 <= sp2 <= Sp - 128) by (destruct FSP; lia).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & _ & RFC). unfold sh_cover in RFC.
  pose proof (RFD L) as RF50. pose proof (RFW L) as RFW50. unfold sh_cover in RFW50.
  assert (Rlo : Sp - 9136 <= sp2 - 4560 <= sp2) by (destruct FSP; lia).
  assert (Lo8 : (sp2 - 4560) mod 8 = 0)
    by (destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia).
  assert (FRsp : fr + 256 <= sp2 - 4560 \/ sp2 <= fr)
    by (destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)]; [right; lia | left; subst fr sp2; fs_num; lia]).
  pose proof (bytes_at_sub rsegs mc f fb 18 32 BF ltac:(lia)) as BK.
  apply (bytes_at_addr rsegs mc _ (f + 18)) in BK; [|lia].
  fold (cm_blk fb) in BK.
  assert (LK : length (cm_blk fb) = 32%nat) by (unfold cm_blk; rewrite length_firstn, length_skipn; lia).
  destruct (memcmp_model_total (cm_blk fb) (nth i DECLS []) 32 ltac:(lia) ltac:(rewrite cm_decl_len; lia))
    as [v Hv].
  pose proof (mm_spec 32 (cm_blk fb) (nth i DECLS []) v LK (cm_decl_len i Hi) Hv) as [MM VR].
  do 4 step.
  eapply evtF_cut.
  { eapply HBC with (RNG := RNG) (ls := cm_blk fb) (rs := nth i DECLS []) (v := v) (lo := sp2 - 4560).
    all: cbv zeta.
    all: rewrite ?unsigned_lit by lia.
    all: unfold BCMP_WRAP_K.
    all: lazymatch goal with
         | |- bytes_at _ _ _ _ => first [exact BK | exact BB | exact C1 | exact C2 | exact C3 | exact C4 | exact C5]
         | |- memcmp_model _ _ _ = Some _ => exact Hv
         | |- mem_inv _ _ => exact MIg
         | |- asan_cells _ => exact ACg
         | |- shadow_rw_on _ _ =>
             exact (shadow_rw_on_mono _ _ mc (cmOn_R_bcmp f len Sp FS fr sp2 jj nn L FK) (cmSRT_R mc SRg))
         | |- stk _ _ _ _ => apply (cm_stk_sub mc (Sp - 9136) Sp); [exact STWg | lia | lia]
         | |- addressable _ _ _ =>
             first [ exact ADo | exact (acl_addr_sub mc f 50 (f + 18) 32 AF ltac:(lia) ltac:(lia) ltac:(lia)) ]
         | |- end_in_app _ _ =>
             right; first [ replace (f + 18 + 32) with (f + 50) by lia; exact APf50
                          | replace (fr + 112 + 32) with (fr + 144) by lia; apply FAP; lia ]
         | |- rng_bytes _ => exact RB
         | |- rng _ _ _ =>
             first [ exact RIMG | apply (rng_sub RNG _ _ _ _ RF50); lia | apply (rng_sub RNG _ _ _ _ RFR); lia
                   | apply (rng_sub RNG _ _ _ _ RWIN); lia ]
         | |- _ = 0 \/ rng _ _ _ =>
             right; rewrite ?(Z.mul_comm 8); first [ apply RFW50; lia | apply RFC; lia ]
         | |- _ = 0 \/ app_mem _ =>
             right; first [ replace (f + 18 + 7) with (f + 25) by lia;
                            exact (acl_app_in mc f 50 25 AF ltac:(lia))
                          | replace (fr + 112 + 7) with (fr + 119) by lia; apply FAP; lia ]
         | |- _ \/ _ => first [ destruct Hfd; [left; lia | right; destruct FSP; lia]
                              | destruct FRsp; [left; lia | right; lia] ]
         | |- _ => unfold HIGHMEM_BEG, APPMEM_END; lia
         end. }
  intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m'' & -> &
              MUb & WMb & MIb & STb & ACb & SRb & _ & _).
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite ?(unsigned_lit sp2) in MUb, STb by lia.
  unfold BCMP_WRAP_K in MUb, STb.
  apply K; [| exact VR | exact MM].
  exact (cm_win_inv fr sp2 jj nn mc m'' (sp2 - 4560) INVk Rlo Lo8 MUb WMb MIb STb (cmSRT_step mc m'' SRg SRb)).
Qed.

(* The turn's result, from the return of reac_box_model_block for row i (0x8509c) to the next cut: the row is a
   declaration, the input's 32 bytes at f + 18 are compared with it (cm_bc), and the four shadow bytes 14..17 of the
   frame := 0xf8 make the buffer unusable again.  A match, and the eleventh miss, end at the exit state
   (cm_tail_K); any other miss ends at the call of reac_box_model_block for row S i (cm_turn_head), with the loop's
   facts carried to it. *)
Lemma cm_post_mb_K : forall (k : nat), cm_gate len fb = true ->
  forall (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte) (w4 w9 : word)
         (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
  w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w9 = Z_to_bv 64 (Z.of_nat k) ->
  (i + k = 11)%nat -> (0 < k)%nat ->
  (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  cmInv fr sp2 jj nn mc -> bytes_at rsegs mc (fr + 112) (nth i DECLS []) -> addressable mc (fr + 112) 32 ->
  evtF rsegs RNG
    (fun ms => cm_exit_at ms \/
       exists (k' : nat) (m0 : word -> option byte) (v4 v9 : word)
              (zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
         ms = MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp zt0 zt1 zt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                      v4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) za3 za4 za5 za6 za7
                      (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) v4 (Z_to_bv 64 (fr + 112))
                      (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) v9 (Z_to_bv 64 1)
                      (Z_to_bv 64 (-8)) zt3 zt4 zt5 zt6)
                 F (Z_to_bv 64 0x865d8) fc None m0 (seg_rom rsegs) /\
         v4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat (S i)) /\ v9 = Z_to_bv 64 (Z.of_nat k') /\
         (S i + k' = 11)%nat /\ (0 < k')%nat /\
         (forall j, (j < S i)%nat -> nth j DECLS [] <> cm_blk fb) /\
         cmAtMB (S i) fr sp2 jj nn m0)
    (MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             (Z_to_bv 64 1) ya1 ya2 ya3 ya4 ya5 ya6 ya7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
        F (Z_to_bv 64 0x8509c) fc None mc (seg_rom rsegs)).
Proof.
  intros k G i fr sp2 jj nn mc w4 w9 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
    E4 E9 Hik Hk Hnd INV2 BB2 AD2.
  destruct k as [|k]; [lia|].
  subst w4 w9.
  assert (Hi : (i < 11)%nat) by lia.
  pose proof INV2 as (FKl & _). pose proof (cm_fr_rng fr sp2 jj nn FKl) as (RFR & RFS & _). clear FKl.
  pose proof (cm_gate_len G) as L.
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  (* 0x8509c: the row is a declaration, so the test against s10 = 1 falls through *)
  step. if_false.
  (* 0x850a0, 0x850a4: the wrap test of the input pointer (not taken) *)
  step. step.
  rewrite cm_ltu_neg_l by lia.
  replace (-19 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  (* 0x850a8 .. 0x850b4: the call of the bcmp wrapper *)
  eapply (cm_bc _ i fr sp2 jj nn); [exact Hi | exact L | exact INV2 | exact BB2 | exact AD2 |].
  intros mc2 v zt0 zt1 zt2 za1 za2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 INV3 VR MM.
  (* 0x850b8: the result of the comparison *)
  step. rewrite cm_eqb0 by lia.
  destruct (Z.eqb_spec v 0) as [V0|V0]; cbv iota.
  - (* the match: 0x85240, the four shadow bytes := 0xf8, then the tail to the exit state *)
    destruct (cm_shst_pre _ _ _ _ _ INV3)
      as (_ & _ & _ & FAP3 & FSW3 & SHlo3 & SHhi3 & WM3 & MI3 & STW3 & STF3 & STS3).
    assert (MU3 : munch (cmHF fr) mc2 mc2) by apply munch_refl.
    assert (WH3 : wmono rsegs mc2 mc2) by apply wmono_refl.
    unfold cmHF in MU3.
    step.
    cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
    step.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (RM3 : rd_mono mc2 mf) by (cm_rdm MU3 STW3 STF3 STS3) end.
    eapply evtF_mono;
      [ apply (cm_tail_K fr sp2 jj nn _ (CM_T + 296 * Z.of_nat i));
        [ symmetry; apply cm_want_hit; [exact G | exact Hi | symmetry; exact (proj1 MM V0) | exact Hnd]
        | eapply cm_inv_step; [exact INV3 | exact MU3 | exact WH3 | exact RM3 | exact MI3] ]
      | intros msx Hx; cbv beta; left; exact Hx ].
  - (* no match: 0x850bc, the four shadow bytes := 0xf8, then the next row's call or the tail with 0 *)
    assert (Hne : nth i DECLS [] <> cm_blk fb) by (intros Hq; apply V0; apply (proj2 MM); symmetry; exact Hq).
    destruct (cm_shst_pre _ _ _ _ _ INV3)
      as (_ & _ & _ & FAP3 & FSW3 & SHlo3 & SHhi3 & WM3 & MI3 & STW3 & STF3 & STS3).
    assert (MU3 : munch (cmHF fr) mc2 mc2) by apply munch_refl.
    assert (WH3 : wmono rsegs mc2 mc2) by apply wmono_refl.
    unfold cmHF in MU3.
    cm_wst (shadow_addr fr + 14) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 15) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 16) 1%nat. step. store_done.
    cm_wst (shadow_addr fr + 17) 1%nat. step. store_done.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
      assert (RM3 : rd_mono mc2 mf) by (cm_rdm MU3 STW3 STF3 STS3);
      assert (INV4 : cmInv fr sp2 jj nn mf)
        by (eapply cm_inv_step; [exact INV3 | exact MU3 | exact WH3 | exact RM3 | exact MI3])
    end.
    step. step. step.
    rewrite cm_eqb_lit by lia.
    match goal with |- evtF _ _ _ (MS _ _ (if negb (?e =? 0) then _ else _) _ _ _ _) =>
      destruct (Z.eqb_spec e 0) as [K0|K0] end; cbn [negb]; cbv iota.
    + (* the 11th row was the last: s4 := 0, then the tail to the exit state *)
      assert (Ek : k = 0%nat) by lia. subst k.
      step.
      eapply evtF_mono;
        [ apply (cm_tail_K fr sp2 jj nn _ 0);
          [ symmetry; apply cm_want_none; intros j Hj;
            destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; lia]
          | exact INV4 ]
        | intros msx Hx; cbv beta; left; exact Hx ].
    + (* 0x8507c again: the next row's turn, up to its call of reac_box_model_block *)
      destruct k as [|k]; [lia|].
      eapply evtF_cut;
        [ eapply (cm_turn_head (S i) fr sp2 jj nn);
          [ exact G | lia | f_equal; unfold CM_T in *; lia | exact INV4 ]|].
      intros msx (m0 & -> & HAtMB).
      apply evtF_done. cbv beta. right.
      exists (S k). exists m0. do 14 eexists.
      split; [reflexivity|].
      split; [f_equal; unfold CM_T in *; lia|].
      split; [f_equal; lia|].
      split; [lia|].
      split; [lia|].
      split; [intros j Hj; destruct (Nat.eq_dec j i) as [->|Hji]; [exact Hne | apply Hnd; lia]|].
      exact HAtMB.
Qed.

(* The row loop from the call of reac_box_model_block for row i (0x865d8): the call (cm_mb), the turn's result
   (cm_post_mb_K) and, when the row misses and rows are left, the next row's call. *)
Lemma cm_rows : forall (k : nat), cm_gate len fb = true ->
  forall (i : nat) (fr sp2 jj nn : Z) (m0 : word -> option byte) (w4 w9 : word)
         (rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w9 = Z_to_bv 64 (Z.of_nat k) ->
  (i + k = 11)%nat -> (0 < k)%nat ->
  (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  cmAtMB i fr sp2 jj nn m0 ->
  evtF rsegs RNG cmPost
    (MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             w4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x865d8) fc None m0 (seg_rom rsegs)).
Proof.
  intros k G.
  induction k as [|k IH]; intros i fr sp2 jj nn m0 w4 w9 rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
    E4 E9 Hik Hk Hnd HAt; [lia|].
  eapply (cm_mb cmPost i fr sp2 jj nn m0 w4 w9); [exact (cm_gate_len G) | exact E4 | exact HAt |].
  intros mc' yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 INV2 BB2 AD2.
  eapply evtF_cut;
    [exact (cm_post_mb_K (S k) G i fr sp2 jj nn mc' w4 w9 yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7
              yt3 yt4 yt5 yt6 E4 E9 Hik Hk Hnd INV2 BB2 AD2)|].
  intros msx [EX | (k' & m1 & v4 & v9 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 &
                    -> & E4' & E9' & Hik' & Hk' & Hnd' & HAt')].
  - exact (cm_exit_at_post msx EX).
  - assert (Ek : k' = k) by lia. subst k'.
    apply (IH (S i) fr sp2 jj nn m1 v4 v9 zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6);
      [exact E4' | exact E9' | exact Hik' | exact Hk' | exact Hnd' | exact HAt'].
Qed.

(* (b) The row loop at 0x8507c: at most 11 turns (s9 counts down, s4 = CM_T + 296 i). Each turn marks the 32-byte
   buffer at fr + 112 usable (the four shadow bytes 14..17 := 0), builds the row's declaration there
   (reac_box_model_block), compares it with the input's 32 bytes at f + 18 (the bcmp wrapper) and marks the buffer
   unusable again (the four shadow bytes := 0xf8). A match keeps s4 (the row's address), the 11th miss sets it to 0.
   The first turn's head is cm_turn_head, the rest of the loop cm_rows. *)
Lemma cm_loop : forall (k : nat), cm_gate len fb = true ->
  forall (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte) (w4 w9 : word)
         (rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6 : word),
  w4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat i) -> w9 = Z_to_bv 64 (Z.of_nat k) ->
  (i + k = 11)%nat -> (0 < k)%nat ->
  (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG cmPost
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) w4 (Z_to_bv 64 (fr + 112))
             (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) w9 (Z_to_bv 64 1)
             (Z_to_bv 64 (-8)) rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x8507c) fc None mc (seg_rom rsegs)).
Proof.
  intros k G.
  intros i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6
    E4 E9 Hik Hk Hnd INVk.
  eapply evtF_cut;
    [exact (cm_turn_head i fr sp2 jj nn mc w4 w9 rra rt0 rt1 rt2 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
              rt3 rt4 rt5 rt6 G ltac:(lia) E4 INVk)|].
  intros ms (m0 & -> & HAt).
  apply (cm_rows k G i fr sp2 jj nn m0 w4 w9 rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rt3 rt4 rt5 rt6);
    [exact E4 | exact E9 | exact Hik | exact Hk | exact Hnd | exact HAt].
Qed.

(* ============================ the gate, the header bytes and the parse call ============================ *)

(* A short input or a header byte other than 0x88 / 0x19 / 0xcd / 0xea at 12 / 13 / 16 / 17 makes the gate false,
   so the result is 0. *)
Lemma cm_miss_short : len < 50 -> want CM_T len fb = 0.
Proof. intros Hl. apply cm_gate_false. unfold cm_gate. rewrite (proj2 (Z.leb_gt 50 len) Hl). reflexivity. Qed.

Lemma cm_miss_hdr : forall k c, 50 <= len ->
  (k = 12%nat /\ c = 136 \/ k = 13%nat /\ c = 25 \/ k = 16%nat /\ c = 205 \/ k = 17%nat /\ c = 234) ->
  bv_unsigned (nth k fb (Z_to_bv 8 0)) <> c -> want CM_T len fb = 0.
Proof.
  intros k c Hl Hk Hne. apply cm_gate_false. unfold cm_gate, cp_v, cp_b, cp_z.
  rewrite (proj2 (Z.leb_le 50 len) Hl).
  destruct Hk as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]; rewrite (proj2 (Z.eqb_neq _ _) Hne);
    rewrite ?andb_false_r; reflexivity.
Qed.

(* The instrumented check of a single byte (as lib/A/Prog/reac_ctrl_classify_box_frame.v): the shadow byte k is
   loaded and the access goes on when k = 0 or (X mod 8) < k; the call of __asan_report_* is not reached. *)
Ltac chk_core X RX r SH pre extra :=
  let k := fresh "k" in let RK := fresh "RK" in let OK := fresh "OK" in let KR := fresh "KR" in
  destruct SH as (k & RK & OK & KR);
  pre X RX; steps_until_if; clear RK;
  unfold sxb; rewrite (rc_eqb0_signed (bv_signed k)) by (clear -KR; lia);
  lazymatch goal with
  | |- evtF ?segs ?RG ?Q (MS ?R ?F (if _ then _ else ?B) ?fc ?rv ?mm ?ro) =>
      let G := fresh "G" in
      enough (G : forall rr : word, evtF segs RG Q (MS (bvmap_set r rr R) F B fc rv mm ro));
      [ let K0 := fresh "K0" in
        destruct (Z.eqb_spec (bv_signed k) 0) as [K0|K0]; cbn [negb];
        [ bjoin G r
        | step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_land7; extra X;
          step;
          let MB := fresh "MB" in pose proof (Z.mod_pos_bound X 8 eq_refl) as MB;
          rewrite (rc_lts_signed (X mod 8) (bv_signed k)) by (clear -MB KR; lia);
          replace (X mod 8 <? bv_signed k) with true
            by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK]; [exfalso; exact (K0 OK) | clear -OK; lia]);
          clear MB; bjoin G r ]
      | intros ?; simp_regs; clear OK KR ]
  end.

Ltac pre_sr X RX := step; rewrite ?(unsigned_lit X) by (clear -RX; lia); rewrite rc_shr3.
Ltac no_extra X := idtac.

(* The input buffer and a part of the frame are apart (the frame is in the window or a class-2 side-stack frame,
   which the data range (f, f + 50) is apart from). *)
Lemma cm_f_fr : forall fr sp2 jj nn, cmFK fr sp2 jj nn -> 50 <= len -> fr + 256 <= f \/ f + 50 <= fr.
Proof.
  intros fr sp2 jj nn FK L.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj).
  unfold FS_SIZE in FShi.
  assert (INd : In (f, f + 50) aDf)
    by (unfold aDf; destruct (Z.ltb_spec len 50) as [Hlt|Hlt]; [lia | left; reflexivity]).
  destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)].
  - destruct Hfd as [Hd|Hd]; [right; lia | left; lia].
  - pose proof (fl_dj_out_r aDf (fp_w [0%nat; 1%nat; 2%nat] FS) f (f + 50) f FSdj INd ltac:(lia)) as Ho.
    pose proof (out_in _ _ _ _ Ho (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as Hni.
    pose proof (fl_dj_out_r aDf (fp_w [0%nat; 1%nat; 2%nat] FS) f (f + 50) (f + 49) FSdj INd ltac:(lia)) as Ho2.
    pose proof (out_in _ _ _ _ Ho2 (fpw3_in_frame FS 2 ltac:(cbn; tauto))) as Hni2.
    subst fr. fs_num. lia.
Qed.

(* The state at the call of reac_ctrl_parse at 0x85054 (callee entry 0x83e04, return 0x85058): the length and the
   four header bytes checked, the frame invariant at the call memory and the parse buffer [fr + 32, fr + 68)
   addressable. *)
Definition cmAtParse (fr sp2 jj nn : Z) (m0 : word -> option byte) : Prop :=
  50 <= len /\
  bv_unsigned (nth 12 fb (Z_to_bv 8 0)) = 136 /\ bv_unsigned (nth 13 fb (Z_to_bv 8 0)) = 25 /\
  bv_unsigned (nth 16 fb (Z_to_bv 8 0)) = 205 /\ bv_unsigned (nth 17 fb (Z_to_bv 8 0)) = 234 /\
  cmInv fr sp2 jj nn m0 /\ addressable m0 (fr + 32) 36.

(* The post of reac_ctrl_parse_contract_F_on (lib/B/Prog/reac_ctrl_parse_c.v) at this call (o = fr + 32, S = sp2),
   without its asan_cells conjunct. *)
Definition cm_parse_post (fr sp2 nn : Z) (rs6 rs9 rs10 rs11 : word) (m0 : word -> option byte)
    (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mp : word -> option byte),
    ms' = MS (mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp t0' t1' t2' (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                  (Z_to_bv 64 (fst (ctrlparse len fb))) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                  rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 t3' t4' t5' t6')
             F (ret_pc (Z_to_bv 64 0x85058)) fc None mp (seg_rom rsegs) /\
    munch (reac_ctrl_parse_fp (fr + 32) sp2 ++ fp_w [1%nat] FS ++
           [(shadow_addr (sp2 - REAC_CTRL_PARSE_K), shadow_addr sp2)]) m0 mp /\
    wmono rsegs m0 mp /\ mem_inv rsegs mp /\ stk rsegs mp (sp2 - REAC_CTRL_PARSE_K) sp2 /\
    rw_cells rsegs mp (fr + 32) [CB 36 (snd (ctrlparse len fb))] /\
    (forall P, shadow_rw_on P m0 -> shadow_rw_on P mp) /\ addressable mp (sp2 - REAC_CTRL_PARSE_K) REAC_CTRL_PARSE_K /\
    fp [1%nat] mp (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2 (reac_ctrl_parse_W (fr + 32) sp2)
      (reac_ctrl_parse_D f len (fr + 32)) /\
    reac_ctrl_parse_tls mp (bv_unsigned tp) FS (sp2 - REAC_CTRL_PARSE_K) sp2.

(* The stretch from the gate 0x84f88 to the call of reac_ctrl_parse: the length test, the wrap tests of f, the four
   header-byte checks (each miss reaches the exit 0x850fc with s4 = 0: cm_exit_at) and the five shadow stores that
   mark the parse buffer usable. *)
Lemma cm_pre_parse : forall (fr sp2 jj nn : Z) (mc : word -> option byte)
    (rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
  cmInv fr sp2 jj nn mc ->
  evtF rsegs RNG
    (fun ms => cm_exit_at ms \/
       exists m0, ms =
         MS (mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
                 rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x83e04) fc None m0 (seg_rom rsegs) /\ cmAtParse fr sp2 jj nn m0)
    (MS (mkR rra (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
             ra0 ra1 (Z_to_bv 64 50) ra3 ra4 ra5 ra6 ra7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (wa ASAN_K)
             rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
        F (Z_to_bv 64 0x84f88) fc None mc (seg_rom rsegs)).
Proof.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 INVk.
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  pose proof Rf as Rfb. pose proof Rlen as Rlenb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  pose proof INVk as INVc.
  destruct INVc as (FK & _ & _ & MIg0 & (ACg0 & SRg0 & FPg0 & TLg0) & AWXg0 & EXTg0 & STWg0 & STFg0 & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup). unfold ASAN_GT in FRgt.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & _ & FAP & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj0).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  (* 0x84f88: the length gate *)
  step. rewrite cm_ltu_lit by lia.
  destruct (Z.ltb_spec len 50) as [Lshort|L]; cbv iota.
  { step. apply evtF_done. cbv beta. left.
    apply (cm_exit_at_intro fr sp2 jj nn mc 0); [symmetry; exact (cm_miss_short Lshort) | exact INVk]. }
  destruct EXTg0 as (EF & EAT & EBT & EBC & ECL).
  destruct (EF L) as (BF & AF).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  destruct (AFU L) as (_ & APf50).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & RFC).
  pose proof (RFD L) as RF50.
  pose proof (RFW L f 50 ltac:(lia) ltac:(lia) ltac:(lia)) as RFW0.
  (* 0x84f8c .. 0x84f94: the wrap tests of the input pointer (not taken) *)
  step. rewrite (rc_neq0_64 f) by lia. cbv iota.
  step. step. rewrite cm_ltu_neg_r by lia.
  replace (f <? -12 + 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  (* the four header bytes *)
  pose proof (rd_byte rsegs mc f fb 12 BF ltac:(rewrite Hfb; clear; lia)) as R12.
  pose proof (rd_byte rsegs mc f fb 13 BF ltac:(rewrite Hfb; clear; lia)) as R13.
  pose proof (rd_byte rsegs mc f fb 16 BF ltac:(rewrite Hfb; clear; lia)) as R16.
  pose proof (rd_byte rsegs mc f fb 17 BF ltac:(rewrite Hfb; clear; lia)) as R17.
  change (Z.of_nat 12) with 12 in R12. change (Z.of_nat 13) with 13 in R13.
  change (Z.of_nat 16) with 16 in R16. change (Z.of_nat 17) with 17 in R17.
  pose proof (byte_range (nth 12 fb (Z_to_bv 8 0))) as BR12.
  pose proof (byte_range (nth 13 fb (Z_to_bv 8 0))) as BR13.
  pose proof (byte_range (nth 16 fb (Z_to_bv 8 0))) as BR16.
  pose proof (byte_range (nth 17 fb (Z_to_bv 8 0))) as BR17.
  assert (RX12 : 0 <= f + 12 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  assert (RX13 : 0 <= f + 13 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  assert (RX16 : 0 <= f + 16 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  assert (RX17 : 0 <= f + 17 < 2 ^ 64) by (clear -Hf0 Hf50; lia).
  pose proof (acl_shadow mc f 50 12 1 (f + 12) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 12) 8 eq_refl); clear -H; lia) eq_refl) as SH12.
  pose proof (acl_shadow mc f 50 13 1 (f + 13) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 13) 8 eq_refl); clear -H; lia) eq_refl) as SH13.
  pose proof (acl_shadow mc f 50 16 1 (f + 16) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 16) 8 eq_refl); clear -H; lia) eq_refl) as SH16.
  pose proof (acl_shadow mc f 50 17 1 (f + 17) AF ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)
    ltac:(pose proof (Z.mod_pos_bound (f + 17) 8 eq_refl); clear -H; lia) eq_refl) as SH17.
  (* byte 12: 0x88 *)
  step.
  pose proof (shc_byte RNG f 50 (f + 12) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 12) RX12 (Z_to_bv 5 12) SH12 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 12 fb (Z_to_bv 8 0))) 136) as [E12|E12]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 12%nat 136 L ltac:(clear; lia) E12) | exact INVk]. }
  (* byte 13: 0x19 *)
  step. step. rewrite cm_ltu_neg_l by lia.
  replace (-14 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step.
  pose proof (shc_byte RNG f 50 (f + 13) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 13) RX13 (Z_to_bv 5 12) SH13 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 13 fb (Z_to_bv 8 0))) 25) as [E13|E13]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 13%nat 25 L ltac:(clear; lia) E13) | exact INVk]. }
  (* byte 16: 0xcd *)
  step. step. rewrite cm_ltu_neg_l by lia.
  replace (-17 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step.
  pose proof (shc_byte RNG f 50 (f + 16) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 16) RX16 (Z_to_bv 5 12) SH16 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 16 fb (Z_to_bv 8 0))) 205) as [E16|E16]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 16%nat 205 L ltac:(clear; lia) E16) | exact INVk]. }
  (* byte 17: 0xea *)
  step. step. rewrite cm_ltu_neg_l by lia.
  replace (-18 + 2 ^ 64 <? f) with false by (symmetry; apply Z.ltb_ge; lia). cbv iota.
  step.
  pose proof (shc_byte RNG f 50 (f + 17) ltac:(lia) RFW0) as RSy. pose proof RSy as RSy'. unfold ASAN_K in RSy'.
  chk_core (f + 17) RX17 (Z_to_bv 5 12) SH17 pre_sr no_extra.
  step. step. step.
  clear RSy RSy'.
  rewrite cm_eqb_zxb by (clear; lia).
  destruct (Z.eqb_spec (bv_unsigned (nth 17 fb (Z_to_bv 8 0))) 234) as [E17|E17]; cbn [negb]; cbv iota.
  2: { step. apply evtF_done. cbv beta. left. apply (cm_exit_at_intro fr sp2 jj nn mc 0);
       [symmetry; exact (cm_miss_hdr 17%nat 234 L ltac:(clear; lia) E17) | exact INVk]. }
  clear R12 R13 R16 R17 BR12 BR13 BR16 BR17 RX12 RX13 RX16 RX17.
  (* 0x85030 .. 0x85048: the parse buffer at fr + 32 is marked usable (shadow bytes 4..8 := 0,0,0,0,4) *)
  clear EF EAT EBT EBC ECL BF AF ACg0 SRg0 FPg0 TLg0 AWXg0 MIg0 STWg0 STFg0.
  destruct (cm_shst_pre _ _ _ _ _ INVk)
    as (FR8 & _ & _ & FAPc & FSWm & SHlo & SHhi & WMm & MIg & STWg & STFg & STSH).
  assert (MUh : munch (cmHF fr) mc mc) by apply munch_refl.
  assert (WMh : wmono rsegs mc mc) by apply wmono_refl.
  unfold cmHF in MUh.
  step.
  cm_wst (shadow_addr fr + 4) 1%nat. step. cm_keep B4.
  cm_wst (shadow_addr fr + 5) 1%nat. step. cm_keep B5.
  cm_wst (shadow_addr fr + 6) 1%nat. step. cm_keep B6.
  cm_wst (shadow_addr fr + 7) 1%nat. step. cm_keep B7.
  step.
  cm_wst (shadow_addr fr + 8) 1%nat. step. cm_keep B8.
  step. step.
  match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mf _) =>
    assert (RM1 : rd_mono mc mf) by (cm_rdm MUh STWg STFg STSH);
    assert (INV1 : cmInv fr sp2 jj nn mf)
      by (eapply cm_inv_step; [exact INVk | exact MUh | exact WMh | exact RM1 | exact MIg]);
    assert (AD1 : addressable mf (fr + 32) 36)
      by (apply (cm_parse_addr mf fr FR8 ltac:(lia) ltac:(unfold APPMEM_END; lia)
                   ltac:(intros ii Hii; replace (fr + 32 + ii) with (fr + (32 + ii)) by lia; apply FAPc; lia));
          [exact B4 | exact B5 | exact B6 | exact B7 | exact B8])
  end.
  clear B4 B5 B6 B7 B8 MUh WMh RM1.
  (* 0x85054: the call *)
  step.
  apply evtF_done. cbv beta. right. eexists. split; [reflexivity|].
  exact (conj L (conj E12 (conj E13 (conj E16 (conj E17 (conj INV1 AD1)))))).
Qed.

(* From the return of reac_ctrl_parse (0x85058) to the next two cuts: the parse result test, then either the tail
   (cm_tail_K, when the result is not 9), which ends at the exit state 0x850fc, or the loop's registers and the
   first turn's head (cm_turn_head), which ends at the call of reac_box_model_block for row 0. *)
Lemma cm_post_parse_K : forall (fr sp2 jj nn : Z) (mc : word -> option byte) (rs6 rs9 rs10 rs11 : word)
    (ms' : machine_state),
  cmAtParse fr sp2 jj nn mc -> cm_parse_post fr sp2 nn rs6 rs9 rs10 rs11 mc ms' ->
  evtF rsegs RNG
    (fun ms => cm_exit_at ms \/
       exists (m0 : word -> option byte) (v4 v9 : word)
              (zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
         ms = MS (mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp zt0 zt1 zt2 (Z_to_bv 64 Sp) (Z_to_bv 64 CA)
                      v4 (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) za3 za4 za5 za6 za7
                      (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) v4 (Z_to_bv 64 (fr + 112))
                      (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) v9 (Z_to_bv 64 1)
                      (Z_to_bv 64 (-8)) zt3 zt4 zt5 zt6)
                 F (Z_to_bv 64 0x865d8) fc None m0 (seg_rom rsegs) /\
         cm_gate len fb = true /\ v4 = Z_to_bv 64 (CM_T + 296 * Z.of_nat 0) /\
         v9 = Z_to_bv 64 (Z.of_nat 11) /\ cmAtMB 0 fr sp2 jj nn m0)
    ms'.
Proof.
  intros fr sp2 jj nn mc rs6 rs9 rs10 rs11 ms' HAt PO.
  destruct HAt as (L & E12 & E13 & E16 & E17 & INV1 & AD1).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  pose proof Rf as Rfb. pose proof Rlen as Rlenb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  pose proof INV1 as INVc.
  destruct INVc as (FK & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup). unfold ASAN_GT in FRgt.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & _ & FAP & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj0).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  assert (Rlo : Sp - 9136 <= sp2 - 8800 <= sp2) by (destruct FSP; lia).
  assert (Rsp2b : Sp - 336 <= sp2 <= Sp - 128) by (destruct FSP; lia).
  assert (Lo8 : (sp2 - 8800) mod 8 = 0)
    by (destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia).
  destruct PO as (p0 & p1 & p2 & pa1 & pa2 & pa3 & pa4 & pa5 & pa6 & pa7 & p3 & p4 & p5 & p6 & mp & -> &
                  MUp & WMp & MIp' & STp & RWp & SRp' & ADp & FPp' & TLp').
  rewrite ret_pc_even by (try lia; reflexivity).
  rewrite ?unsigned_lit in MUp, STp, ADp, FPp', TLp' by lia.
  unfold reac_ctrl_parse_fp in MUp. unfold REAC_CTRL_PARSE_K in MUp, STp, ADp.
  replace (fr + 32 =? 0) with false in MUp by (symmetry; apply Z.eqb_neq; lia).
  cbn [app] in MUp.
  replace (fr + 32 + 36) with (fr + 68) in MUp by lia.
  apply (munch_weaken _ (cmCF sp2 (sp2 - 8800) 32 68 1%nat fr)) in MUp;
    [| intros x Hx; unfold cmCF in Hx; cbn [fp_w flat_map fp_w1 app outside] in Hx |- *; tauto].
  pose proof FPp' as FPc.
  destruct FPc as (DTp & TSp & Cp & Tp & DBp & kkp & _ & _ & HPp & _ & _ & HCLp & _).
  pose proof HPp as (_ & _ & _ & _ & STfsp).
  apply Forall_cons_iff in HCLp as [CL1 _].
  assert (INV2 : cmInv fr sp2 jj nn mp).
  { apply (cm_call_inv fr sp2 jj nn _ mp (cmCF sp2 (sp2 - 8800) 32 68 1%nat fr) (sp2 - 8800) 32 68 1%nat
             INV1 ltac:(lia) Rlo Lo8 ltac:(lia) ltac:(lia) MUp ltac:(intros x Hx; exact Hx) WMp MIp' STp).
    - replace (sp2 - (sp2 - 8800)) with 8800 by lia. exact ADp.
    - intros x Hx.
      destruct (cm_bytes_of_rw rsegs mp (fr + 32) 36 (snd (ctrlparse len fb)) RWp) as (BBp & LBp).
      apply (rd_of_bytes mp (fr + 32) _ BBp). rewrite LBp. cbn [Z.of_nat Pos.of_succ_nat]. lia.
    - exact STfsp.
    - exact (cmSRT_step mc mp (cm_inv_srt fr sp2 jj nn mc INV1) SRp').
    - exact CL1. }
  (* 0x85058, 0x8505c: the parse result *)
  step. step.
  pose proof (ctrlparse_kind_range len fb) as KR.
  rewrite cm_eqb_lit by lia.
  destruct (Z.eqb_spec (fst (ctrlparse len fb)) 9) as [K9|K9]; cbn [negb]; cbv iota.
  2: { step.
       eapply evtF_mono;
         [ apply (cm_tail_K fr sp2 jj nn mp 0);
           [ symmetry; apply cm_gate_false; unfold cm_gate, cp_v, cp_b, cp_z;
             rewrite (proj2 (Z.eqb_neq _ _) K9); rewrite !andb_false_r; reflexivity
           | exact INV2 ]
         | intros msx Hx; cbv beta; left; exact Hx ]. }
  assert (G : cm_gate len fb = true).
  { unfold cm_gate, cp_v, cp_b, cp_z. rewrite (proj2 (Z.leb_le 50 len) L), E12, E13, E16, E17, K9. reflexivity. }
  (* 0x85060 .. 0x85078: the loop's registers, then the first turn's head *)
  do 7 step.
  eapply evtF_cut;
    [ eapply (cm_turn_head 0%nat fr sp2 jj nn mp);
      [ exact G | lia
      | first [reflexivity | (unfold CM_T; f_equal; lia) | (vm_compute; reflexivity)]
      | exact INV2 ]|].
  intros msx (m0 & -> & HAtMB).
  apply evtF_done. cbv beta. right.
  exists m0. do 14 eexists.
  split; [reflexivity|].
  split; [exact G|].
  split; [first [reflexivity | (unfold CM_T; f_equal; lia) | (vm_compute; reflexivity)]|].
  split; [first [reflexivity | (f_equal; lia) | (vm_compute; reflexivity)]|].
  exact HAtMB.
Qed.

(* From the return of reac_ctrl_parse (0x85058) to the exit: cm_post_parse_K to the exit state (cm_exit_at_post,
   cm_exit) or to the row loop's first call of reac_box_model_block (cm_rows). *)
Lemma cm_post_parse : forall (fr sp2 jj nn : Z) (mc : word -> option byte) (rs6 rs9 rs10 rs11 : word)
    (ms' : machine_state),
  cmAtParse fr sp2 jj nn mc -> cm_parse_post fr sp2 nn rs6 rs9 rs10 rs11 mc ms' -> evtF rsegs RNG cmPost ms'.
Proof.
  intros fr sp2 jj nn mc rs6 rs9 rs10 rs11 ms' HAt PO.
  eapply evtF_cut; [exact (cm_post_parse_K fr sp2 jj nn mc rs6 rs9 rs10 rs11 ms' HAt PO)|].
  intros ms [EX | (m0 & v4 & v9 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 &
                   -> & G & E4 & E9 & HAtMB)].
  - exact (cm_exit_at_post ms EX).
  - apply (cm_rows 11 G 0%nat fr sp2 jj nn m0 v4 v9 zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6);
      [exact E4 | exact E9 | lia | lia | intros j Hj; lia | exact HAtMB].
Qed.

(* (c) The gate 0x84f88 .. the parse call and its result: cmKB cmPost.  Composed of cm_pre_parse (or a miss, which
   reaches the exit: cm_exit_at), the call (reac_ctrl_parse_contract_F_on) and cm_post_parse. *)
Lemma cm_body : cmKB cmPost.
Proof.
  unfold cmKB.
  intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 INVk.
  eapply evtF_cut;
    [exact (cm_pre_parse fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11
              rt3 rt4 rt5 rt6 INVk)|].
  intros ms [EX | (m0 & -> & HAt)]; [exact (cm_exit_at_post ms EX)|].
  clear INVk mc.
  pose proof HAt as (L & _ & _ & _ & _ & INV1 & AD1).
  pose proof CA_facts as (CA32 & CAlo & CAhi).
  pose proof HAE as HAE'. pose proof HHM as HHM'. pose proof HK as HKb. pose proof RS as RSb.
  pose proof Rf as Rfb. pose proof Rlen as Rlenb.
  unfold APPMEM_END in HAE'. unfold HIGHMEM_BEG in HHM'.
  pose proof INV1 as INVc.
  destruct INVc as (FK & _ & _ & _ & _ & _ & _ & _ & STFg & _ & _).
  pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FRgt & FRup). unfold ASAN_GT in FRgt.
  pose proof (fk_facts fr sp2 jj nn FK) as (FR32 & FRpos & FR192 & _ & FAP & _ & FSP).
  destruct acl_fs as (FSpos & FSmod & FSgt & FShi & FSapp & FSdj0).
  unfold FS_SIZE in FShi. unfold ASAN_GT in FSgt.
  assert (Rsp2 : 0 <= sp2 < 2 ^ 64) by (destruct FSP; lia).
  destruct (HF L) as (Hf0 & Hf50 & _ & Hfd).
  pose proof (cm_fr_rng fr sp2 jj nn FK) as (RFR & RFS & RFC).
  pose proof (RFD L) as RF50.
  pose proof (RFW L f 50 ltac:(lia) ltac:(lia) ltac:(lia)) as RFW0.
  assert (FR8 : fr mod 8 = 0) by (clear -FR32; Z.div_mod_to_equations; lia).
  pose proof FAP as FAPc.
  destruct (cm_rw_stk _ fr (fr + 192) (fr + 32) 36 STFg ltac:(lia) ltac:(cbn; lia)) as (junk & RW1).
  (* 0x85054: the call of reac_ctrl_parse *)
  pose proof INV1 as INV1c.
  destruct INV1c as (_ & _ & _ & MIp & (ACp & SRp & FPp & TLp) & AWXp & EXTp & STWp & STFp & _ & _).
  destruct EXTp as (EFp & EATp & EBTp & EBCp & ECLp).
  destruct (EFp L) as (BFp & AFp).
  destruct ECLp as (C1 & C2 & C3 & C4 & C5).
  assert (Rlo : Sp - 9136 <= sp2 - 8800 <= sp2) by (destruct FSP; lia).
  assert (Rsp2b : Sp - 336 <= sp2 <= Sp - 128) by (destruct FSP; lia).
  lazymatch type of INV1 with cmInv _ _ _ _ ?mp =>
    assert (TLR : forall DT TS C T DB kk, asan_tls_cells mp (bv_unsigned tp) DT TS C T DB kk ->
              Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB kk))
      by (destruct INV1 as (_ & MUa & _); exact (cm_tls_rng mp aWc MUa (fun x Hx => Hx)))
  end.
  pose proof (cm_win_rng (sp2 - 8800) sp2 ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & RPWS).
  assert (Lo8 : (sp2 - 8800) mod 8 = 0)
    by (destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia).
  assert (FRsp : fr + 256 <= sp2 - 8800 \/ sp2 <= fr)
    by (destruct FK as [(Ef & Es & _ & _) | (Hj & Ef & Es & _)]; [right; lia | left; subst fr sp2; fs_num; lia]).
  pose proof (cm_f_fr fr sp2 jj nn FK L) as FRf.
  eapply evtF_cut.
  { eapply HPC with (RNG := RNG) (f := f) (n := len) (o := fr + 32) (S := sp2) (fr := fb) (junk := junk).
    all: cbv zeta.
    all: try reflexivity.
    all: rewrite ?unsigned_lit by lia.
    all: unfold REAC_CTRL_PARSE_K.
    all: lazymatch goal with
         | |- stk _ _ _ _ => apply (cm_stk_sub _ (Sp - 9136) Sp); [exact STWp | lia | lia]
         | |- mem_inv _ _ => exact MIp
         | |- asan_cells _ => exact ACp
         | |- shadow_rw_on _ _ =>
             exact (shadow_rw_on_mono _ _ _ (cmOn_R_parse f len Sp FS fr sp2 jj nn FK) (cmSRT_R _ SRp))
         | |- length _ = _ => exact Hfb
         | |- _ mod 16 = 0 => destruct FSP as [E|E]; rewrite E; clear -CA32; Z.div_mod_to_equations; lia
         | |- addressable _ _ 8800 =>
             exact (cm_awx_addr fr sp2 jj nn _ (sp2 - 8800) 8800 INV1 ltac:(lia) ltac:(lia) ltac:(lia))
         | |- addressable _ REAC_CTRL_PARSE_BC _ => exact EBCp
         | |- bytes_at _ _ _ _ => first [exact C1 | exact C2 | exact C3 | exact C4 | exact C5]
         | |- forall i, In i _ -> _ =>
             intros ii Hii; apply (proj2 (proj2 BFp)); rewrite Hfb;
             pose proof (cp_rd_lt39 len fb ii Hii); lia
         | |- 50 <= len -> addressable _ _ _ => intros _; exact AFp
         | |- 50 <= len -> rng _ _ _ => intros _; first [exact RF50 | exact RFW0]
         | |- _ <> 0 -> rng _ _ _ =>
             intros _; first [ apply (rng_sub RNG _ _ _ _ RFR); lia
                             | exact (RFC (fr + 32) 36 ltac:(lia) ltac:(lia) ltac:(lia)) ]
         | |- rng_bytes _ => exact RB
         | |- rng _ _ _ =>
             first [ exact RIMG | exact RBC | exact RBCW | exact RHDR | exact RPWS
                   | apply (rng_sub RNG _ _ _ _ RWIN); lia ]
         | |- Forall _ (fp_w _ _) => exact (rf_fpw_c 1%nat ltac:(cbn; tauto))
         | |- 50 <= len -> _ =>
             intros _; split; [lia|]; split; [lia|]; destruct Hfd; [left; lia | right; destruct FSP; lia]
         | |- _ <> 0 -> _ mod 4 = 0 /\ _ =>
             intros _; split; [clear -FR8; Z.div_mod_to_equations; lia|];
             split; [lia|]; split; [exact RW1|];
             split; [destruct FRsp; [left; lia | right; lia]|];
             intros _; destruct FRf; [left; lia | right; lia]
         | |- _ <> 0 -> addressable _ _ 36 /\ _ =>
             intros _; split; [exact AD1|];
             split; [replace (fr + 32 + 36) with (fr + 68) by lia; apply FAPc; lia
                    | right; pose proof (cm_fr_bounds fr sp2 jj nn FK) as (FG36 & _);
                      unfold ASAN_GT in FG36; unfold asan_stack_malloc_c.CF; lia]
         | |- fp _ _ _ _ _ _ _ _ =>
             unfold reac_ctrl_parse_W, reac_ctrl_parse_D;
             replace (fr + 32 =? 0) with false by (symmetry; apply Z.eqb_neq; lia);
             replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; lia);
             cbn [app]; replace (fr + 32 + 36) with (fr + 68) by lia;
             apply (cm_fp_callee fr sp2 jj nn _ 1%nat (sp2 - 8800) 32 68 _ INV1 ltac:(lia) Rlo
                      ltac:(lia) ltac:(lia));
             apply fl_dj_cons;
             split; [apply (fp_dj_incl _ (fp_w [0%nat; 1%nat; 2%nat] FS));
                       [apply fp_w_incl; cbn; tauto
                       | apply (fl_dj_sub f (f + 50)); [|lia|lia|lia];
                         destruct acl_fs as (_ & _ & _ & _ & _ & FSdj);
                         unfold aDf in FSdj;
                         replace (len <? 50) with false in FSdj by (symmetry; apply Z.ltb_ge; lia);
                         exact FSdj]|];
             apply fl_dj_cons;
             split; [exact (cm_dj_fr fr sp2 jj nn 32 68 1%nat FK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
                    | constructor]
         | |- reac_ctrl_parse_tls _ _ _ _ _ =>
             exact (cm_tls_callee _ 1%nat (sp2 - 8800) sp2 ltac:(lia) TLp ltac:(lia) ltac:(lia) ltac:(lia))
         | |- _ => first [ exact TLR | lia ]
         end. }
  intros ms' (p0 & p1 & p2 & pa1 & pa2 & pa3 & pa4 & pa5 & pa6 & pa7 & p3 & p4 & p5 & p6 & mp & -> &
              MUp & WMp & MIp' & STp & RWp & ACp' & SRp' & ADp & FPp' & TLp').
  apply (cm_post_parse fr sp2 jj nn m0 rs6 rs9 rs10 rs11 _ HAt).
  exists p0, p1, p2, pa1, pa2, pa3, pa4, pa5, pa6, pa7, p3, p4, p5, p6, mp.
  split; [reflexivity|]. split; [exact MUp|]. split; [exact WMp|]. split; [exact MIp'|].
  split; [exact STp|]. split; [exact (RWp ltac:(lia))|]. split; [exact SRp'|]. split; [exact ADp|].
  split; [exact FPp' | exact TLp'].
Qed.
End MatchF.

(* The footprint contract of reac_box_catalogue_match_c.v in its route-(C) form from the `_on` footprint forms of the
   four callees: the accepted proof, unchanged (cm_entry to the gate, cm_body to cmPost, which is the contract's
   post).  After End Callees the theorem also takes Section Callees' hypothesis HSM2 :
   asan_stack_malloc_2_contract_F_on, so it reads
     asan_stack_malloc_2_contract_F_on -> reac_ctrl_parse_contract_F_on -> reac_box_model_block_contract_F_on ->
     bcmp_wrap_contract_F_on -> reac_box_catalogue_match_contract_F_on. *)
Theorem reac_box_catalogue_match_holds_F_on :
  reac_ctrl_parse_contract_F_on -> reac_box_model_block_contract_F_on -> bcmp_wrap_c_on.bcmp_wrap_contract_F_on ->
  reac_box_catalogue_match_contract_F_on.
Proof.
  intros HPC HMB HBC.
  unfold reac_box_catalogue_match_contract_F_on, REAC_BOX_CATALOGUE_MATCH, CM_K.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    f len S FS fb Ea0 Ea1 Esp Rf Rlen RS S16 HK ST Hwin Hfb HF HT MI AC SR HHM HAE AW AFU AT ABC
    HBCMP HMEMCMP HGOT HCF254 HCF255 FP0 TLS0 RB RIMG RWIN RWSH RFD RFSH RTB RTSH RBC RBCSH RHDR RFPW RTLS.
  subst a0 a1 sp.
  assert (BT : bytes_at rsegs m CM_T CM_TBL).
  { apply (cm_bytes_img rsegs m CM_T 3256 CM_TBL CM_TBL_eq); [unfold CM_T; lia | unfold CM_T; lia |].
    intros a Ha. apply HT. lia. }
  assert (RFW : 50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n)
    by (intros H50 p n H1 H2 H3; exact (shc_sub RNG f 50 p n H1 H2 H3 (RFSH H50))).
  assert (RTW : forall p n, CM_T <= p -> 0 < n -> p + n <= CM_T + 3256 -> sh_cover RNG p n)
    by (intros p n H1 H2 H3; exact (shc_sub RNG CM_T 3256 p n H1 H2 H3 RTSH)).
  assert (RBCW : sh_cover RNG REAC_CTRL_PARSE_BC 6) by exact RBCSH.
  clear RFSH RTSH RBCSH.
  eapply cm_entry; try eassumption.
  apply cm_body; assumption.
Qed.

End Callees.

Print Assumptions reac_box_catalogue_match_holds_F_on.
