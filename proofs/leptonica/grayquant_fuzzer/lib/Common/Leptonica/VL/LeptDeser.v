(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL .
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr LeptBase LeptErr LeptCmap LeptPixDestroy LeptPixHdr LeptPadBitsW LeptPixCreate LeptCmapDeser LeptCmapValid LeptDeserA LeptDeserB.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Musl Require Import MemcpyBase Memcpy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Deser.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {P16 : PinsG}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma str_pixDeserialize : str16 (0x105ea + dVLS_105ea) 24. Proof. rl_dbounds (dVLS_105ea :: nil). str16_tac. Qed.
Lemma str_e2 : str16 (0x10749 + dVLS_10749) 17. Proof. rl_dbounds (dVLS_10749 :: nil). str16_tac. Qed.
Lemma str_e3 : str16 (0x1097f + dVLS_1097f) 13. Proof. rl_dbounds (dVLS_1097f :: nil). str16_tac. Qed.
Lemma str_e4 : str16 (0x1034c + dVLS_1034c) 14. Proof. rl_dbounds (dVLS_1034c :: nil). str16_tac. Qed.
Lemma str_e5 : str16 (0x10322 + dVLS_10322) 14. Proof. rl_dbounds (dVLS_10322 :: nil). str16_tac. Qed.
Lemma str_e6 : str16 (0x1079f + dVLS_1079f) 15. Proof. rl_dbounds (dVLS_1079f :: nil). str16_tac. Qed.
Lemma str_e7 : str16 (0x10488 + dVLS_10488) 21. Proof. rl_dbounds (dVLS_10488 :: nil). str16_tac. Qed.
Lemma str_e9 : str16 (0x10807 + dVLS_10807) 12. Proof. rl_dbounds (dVLS_10807 :: nil). str16_tac. Qed.
Lemma str_e10 : str16 (0x10a7c + dVLS_10a7c) 13. Proof. rl_dbounds (dVLS_10a7c :: nil). str16_tac. Qed.
Lemma str_e12 : str16 (0x103ef + dVLS_103ef) 24. Proof. rl_dbounds (dVLS_103ef :: nil). str16_tac. Qed.
Lemma str_e1 : str16 (0x10726 + dVLS_10726) 34. Proof. rl_dbounds (dVLS_10726 :: nil). str16_tac. Qed.
Lemma str_e8 : str16 (0x104ff + dVLS_104ff) 83. Proof. rl_dbounds (dVLS_104ff :: nil). str16_tac. Qed.

Lemma et_str : forall pc msg, In (pc, msg) et_leaves -> exists k, str16 msg k.
Proof.
  intros pc msg Hin. unfold et_leaves in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; injection E; intros <- <-.
  - exists 17%Z; exact str_e2.
  - exists 13%Z; exact str_e3.
  - exists 14%Z; exact str_e4.
  - exists 14%Z; exact str_e5.
  - exists 15%Z; exact str_e6.
  - exists 21%Z; exact str_e7.
Qed.
Lemma ej_str : forall pc msg, In (pc, msg) ej_leaves -> exists k, str16 msg k.
Proof.
  intros pc msg Hin. unfold ej_leaves in Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[]]]]; injection E; intros <- <-.
  - exists 12%Z; exact str_e9.
  - exists 13%Z; exact str_e10.
  - exists 24%Z; exact str_e12.
Qed.

(* [comment removed for export] *)
Definition svr (regs : bvmap 5 word) (i : nat) : word :=
  match i with 8 => getr regs 8 | 9 => getr regs 9 | 18 => getr regs 18 | 19 => getr regs 19 | 20 => getr regs 20
  | 21 => getr regs 21 | 22 => getr regs 22 | _ => getr regs 23 end%nat.
Definition frame9 (s : Z) (ret : word) (sv : nat -> word) : list (Z * word) :=
  [((s - 8)%Z, ret); ((s - 16)%Z, sv 8%nat); ((s - 24)%Z, sv 9%nat); ((s - 32)%Z, sv 18%nat); ((s - 40)%Z, sv 19%nat); ((s - 48)%Z, sv 20%nat);
   ((s - 56)%Z, sv 21%nat); ((s - 64)%Z, sv 22%nat); ((s - 72)%Z, sv 23%nat)].

Lemma cells_FR9 : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FR9 m s ret regs) (frame9 s ret (svr regs)).
Proof. intros m s ret regs Hs Hs64. unfold frame9, FR9, svr. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Lemma pd_cells_of : forall m s ret sv, cellsZ m (frame9 s ret sv) -> pd_cells m s ret sv.
Proof. intros m s ret sv CE. unfold frame9 in CE. cbn [cellsZ] in CE. destruct CE as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & _). repeat (split; [assumption|]). assumption. Qed.

Lemma frame9_bounds : forall s ret sv, (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  Forall (fun av => s - 72 <= fst av /\ fst av + 8 <= 2 ^ 64)%Z (frame9 s ret sv).
Proof. intros s ret sv Hs Hs64. unfold frame9. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil. Qed.

Lemma cells_frm : forall C s' m m' s ret sv, Cok C -> FRM C s' m m' -> (c_top C - LSTK <= s')%Z -> (s' <= s - 72)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frame9 s ret sv) -> cellsZ m' (frame9 s ret sv).
Proof.
  intros C s' m m' s ret sv CK F H1 H2 Hs Hs64 CE. apply (cellsZ_frm C s' m m' _ CK F H1); [|exact CE].
  eapply Forall_impl; [|exact (frame9_bounds s ret sv Hs Hs64)]. intros [a v] [X Y]; cbn [fst snd] in *. lia.
Qed.

Lemma cells_out : forall m m' (lo hi : Z) s ret sv, (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 72 \/ s <= lo)%Z -> (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cellsZ m (frame9 s ret sv) -> cellsZ m' (frame9 s ret sv).
Proof.
  intros m m' lo hi s ret sv OUT Hd Hs Hs64 CE. apply (cellsZ_out m m' lo hi _ OUT); [|exact CE].
  unfold frame9. repeat (apply Forall_cons; [cbn [fst snd]; lia |]). apply Forall_nil.
Qed.

(* [comment removed for export] *)
Definition payload (C : lctx) (dp : Z) (pl : list byte) : Prop :=
  live (c_A0 C) (Z_to_bv 64 dp) = Some (Z.of_nat (length pl)) /\ bytes_at (c_m0 C) dp pl /\ (1 <= dp)%Z /\ (dp + Z.of_nat (length pl) < 2 ^ 64)%Z.

Lemma payload_at : forall C A m md dp pl, W C A m md -> payload C dp pl -> bytes_at m dp pl.
Proof.
  intros C A m md dp pl HW (L & B & Hdp & Hhi) i Hi. rewrite <- (B i Hi).
  pose proof (w_live0 _ _ _ _ HW (Z_to_bv 64 dp) _ i L Hi) as E. unfold at_ in E. rewrite u_Z2bv in E by lia. exact E.
Qed.

Lemma payload_field : forall m dp pl (o : nat), bytes_at m dp pl -> (1 <= dp)%Z -> (dp + Z.of_nat (length pl) < 2 ^ 64)%Z -> (o + 4 <= length pl)%nat ->
  rdn SEGS m (Z_to_bv 64 (dp + Z.of_nat o)) 4 = Some (firstn 4 (skipn o pl)) /\ (0 <= bytes_le_to_Z (firstn 4 (skipn o pl)) < 2 ^ 32)%Z.
Proof.
  intros m dp pl o B Hdp Hhi Ho. split.
  - apply (bytes_at_field SEGS m dp pl o 4 ltac:(lia) ltac:(lia) Ho B).
  - pose proof (bytes_le_to_Z_bound (firstn 4 (skipn o pl))) as X. pose proof (bytes_le_to_Z_nonneg (firstn 4 (skipn o pl))).
    rewrite length_firstn, length_skipn, Nat.min_l in X by lia. cbn in X. lia.
Qed.

Lemma payload_byte : forall m dp pl (o : nat), bytes_at m dp pl -> (1 <= dp)%Z -> (dp + Z.of_nat (length pl) < 2 ^ 64)%Z -> (o < length pl)%nat ->
  rdn SEGS m (Z_to_bv 64 (dp + Z.of_nat o)) 1 = Some [nth o pl (Z_to_bv 8 0)].
Proof.
  intros m dp pl o B Hdp Hhi Ho. cbn [rdn]. rewrite (B (Z.of_nat o)) by lia. rewrite Nat2Z.id. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pixobj (C : lctx) (A A' : AS) (m' : word -> option byte) (pix : Z) (v : pixv) (cv : cmapv) : Prop :=
  PIXat m' pix v /\ p_rc v = 1%Z /\ p_text v = 0%Z /\ (0 < 4 * (p_wpl v * p_h v))%Z /\
  live A' (Z_to_bv 64 pix) = Some 64%Z /\ live A (Z_to_bv 64 pix) = None /\ live (c_A0 C) (Z_to_bv 64 pix) = None /\
  live A' (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z /\ live A (Z_to_bv 64 (p_data v)) = None /\
  live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ p_data v <> pix /\
  (p_cmap v = 0%Z \/
   ((1 <= p_cmap v)%Z /\ CMAPat m' (p_cmap v) cv /\ live A' (Z_to_bv 64 (p_cmap v)) = Some 24%Z /\ live A' (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
    (0 < 4 * c_nalloc cv)%Z /\ live A (Z_to_bv 64 (p_cmap v)) = None /\ live A (Z_to_bv 64 (c_arr cv)) = None /\
    live (c_A0 C) (Z_to_bv 64 (p_cmap v)) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
    p_cmap v <> c_arr cv /\ p_cmap v <> pix /\ c_arr cv <> pix /\ p_data v <> p_cmap v /\ p_data v <> c_arr cv)) /\
  (forall q, q <> Z_to_bv 64 pix -> q <> Z_to_bv 64 (p_data v) -> (p_cmap v <> 0%Z -> q <> Z_to_bv 64 (p_cmap v) /\ q <> Z_to_bv 64 (c_arr cv)) ->
             live A' q = live A q).

(* [comment removed for export] *)
Definition pixfacts (v : pixv) (cv : cmapv) : Prop :=
  v = PIXV (p_w v) (p_h v) (p_d v) (spp_of (p_d v)) (wpl_of (p_w v) (p_d v)) 1%Z 0%Z 0%Z 0%Z 0%Z 0%Z (p_cmap v) (p_data v) /\
  hdr_ok (p_w v) (p_h v) (p_d v) /\ (1 <= p_w v)%Z /\ (1 <= p_h v)%Z /\ (p_cmap v <> 0%Z -> cmap_ok cv).

(* [comment removed for export] *)
Definition DK (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s : Z) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix v cv, getr regs' 10 = Z_to_bv 64 pix /\ pixobj C A A' m' pix v cv /\ pixfacts v cv)) ->
     aroom A' vm' (kR - RK_deser) (bR - RB_deser) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

#[local] Definition pd_rest : list (bv 5) := [3; 4; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma pd_eptr_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (pc msg : Z),
  Cok C -> DK C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_deser) (bR - RB_deser) -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M -> (forall q, live A1 q = live A q) ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  In (pc, msg) ej_leaves ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 pc) M al_rom) (with_vmmaps vm1 md)) S.
Proof. rl_dbounds (dVLS_105ea :: dVL_25134 :: nil).
  intros C A m md regs s ret S kR bR A1 M vm1 r pc msg CK HK Hrm Hrk Hrb Hs16 Hlo Hhi Hret H2 HW PM LQ CE R2 RR Hin.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  destruct (ej_str pc msg Hin) as [km Sm].
  destruct (pd_EJ al_rom pc msg r M Hin (W_sev_got C A1 M _ HW) (W_sev C A1 M _ HW)) as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (returnErrorPtr_W C A1 M _ r1 (s - 96) msg (0x105ea + dVLS_105ea) km 24 (rl dVL_25134 0x255e8) (Z_to_bv 64 0) S CK HW ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(rl_ret_ok_VL) Q10 Q11 Q12 Sm str_pixDeserialize).
  intros m2 r2 HW2 OUT2 GR2 CS2 A10. unfold LSF in OUT2.
  destruct (pd_J7c al_rom r2 m2) as (r3 & RUN3 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  assert (CE2 : cellsZ m2 (frame9 s ret (svr regs))) by (eapply (cells_out M m2); [exact OUT2 | lia | lia | lia | exact CE]).
  destruct (pd_RET al_rom r3 m2 s ret (svr regs) ltac:(lia) ltac:(lia) Hret (pd_cells_of _ _ _ _ CE2) ltac:(csr; reflexivity))
    as (r4 & RUN4 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
  unfold svr in *.
  apply (HK A1 m2 vm1 r4 HW2).
  - apply cs_kept_intro; unfold pd_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C (c_A0 C) A1); [exact (W_sub0 _ _ _ _ HW)|].
    eapply (POSTM_range C A1 M _ m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia].
  - left. split; [csr; reflexivity | exact LQ].
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma pd_tail_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (pc msg : Z),
  Cok C -> DK C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_deser) (bR - RB_deser) -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M -> (forall q, live A1 q = live A q) ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  In (pc, msg) et_leaves ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 pc) M al_rom) (with_vmmaps vm1 md)) S.
Proof. rl_dbounds (dVLS_105ea :: nil).
  intros C A m md regs s ret S kR bR A1 M vm1 r pc msg CK HK Hrm Hrk Hrb Hs16 Hlo Hhi Hret H2 HW PM LQ CE R2 RR Hin.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  destruct (et_str pc msg Hin) as [km Sm].
  destruct (pd_ET al_rom pc msg r M Hin (W_sev_got C A1 M _ HW) (W_sev C A1 M _ HW)) as (r1 & RUN1 & Q10 & Q11 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct (pd_X50 al_rom r1 M s ret (svr regs) ltac:(lia) ltac:(lia) (pd_cells_of _ _ _ _ CE) ltac:(csr; reflexivity))
    as (r2 & RUN2 & V2 & V1 & V12 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  unfold svr in *.
  apply (returnErrorPtr_W C A1 M _ r2 s msg (0x105ea + dVLS_105ea) km 24 ret (Z_to_bv 64 0) S CK HW V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) V12 Sm str_pixDeserialize).
  intros m2 r3 HW2 OUT2 GR2 CS2 A10. unfold LSF in OUT2.
  apply (HK A1 m2 vm1 r3 HW2).
  - apply cs_kept_intro; unfold pd_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C (c_A0 C) A1); [exact (W_sub0 _ _ _ _ HW)|].
    eapply (POSTM_range C A1 M _ m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia].
  - left. split; [exact A10 | exact LQ].
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma pd_lerr_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (fmt retpc : Z) kf,
  Cok C -> DK C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_deser) (bR - RB_deser) -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M -> (forall q, live A1 q = live A q) ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 10 = Z_to_bv 64 fmt -> getr r 11 = rl dVLS_105ea 0x105ea -> getr r 1 = Z_to_bv 64 retpc -> (retpc = (0x251a0 + dVL_25134) \/ retpc = (0x254f4 + dVL_25134))%Z ->
  In fmt (SSP.ls_fmts1 LG) -> str16 fmt kf ->
  realizes SEGS (mkCfg (mkst r (rl dF_13694 0x13694) M al_rom) (with_vmmaps vm1 md)) S.
Proof. rl_dbounds (dVLS_105ea :: dVL_25134 :: nil).
  intros C A m md regs s ret S kR bR A1 M vm1 r fmt retpc kf CK HK Hrm Hrk Hrb Hs16 Hlo Hhi Hret H2 HW PM LQ CE R2 RR R10 R11 R1 Hrp Hin Sf.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  assert (RETOK : ret_ok (Z_to_bv 64 retpc)) by (destruct Hrp as [-> | ->]; rl_ret_ok_VL).
  apply (lept_stderr1_W C A1 M _ r (s - 96) fmt (0x105ea + dVLS_105ea) kf 24 (Z_to_bv 64 retpc) S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) R1 RETOK R10 R11 Hin Sf str_pixDeserialize).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  assert (CE2 : cellsZ m2 (frame9 s ret (svr regs))) by (eapply (cells_out M m2); [exact OUT2 | lia | lia | lia | exact CE]).
  assert (RUNj : exists r3, msteps SEGS (mkst r2 (Z_to_bv 64 retpc) m2 al_rom) (mkst r3 (rl dVL_25134 0x255ec) m2 al_rom) /\ regs_agree (fun _ => False) r2 r3).
  { destruct Hrp as [-> | ->].
    - apply pd_J34.
    - apply pd_J88. }
  destruct RUNj as (r3 & RUN3 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  destruct (pd_R0 al_rom r3 m2) as (r4 & RUN4 & U10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
  destruct (pd_RET al_rom r4 m2 s ret (svr regs) ltac:(lia) ltac:(lia) Hret (pd_cells_of _ _ _ _ CE2) ltac:(csr; reflexivity))
    as (r5 & RUN5 & V2 & V1 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN5 |].
  unfold svr in *.
  apply (HK A1 m2 vm1 r5 HW2).
  - apply cs_kept_intro; unfold pd_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C (c_A0 C) A1); [exact (W_sub0 _ _ _ _ HW)|].
    eapply (POSTM_range C A1 M _ m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia].
  - left. split; [csr; reflexivity | exact LQ].
  - room_tac.
Qed.

(* [comment removed for export] *)
Lemma live_apart : forall C A m md (p q : word) (n k : Z), Cok C -> W C A m md ->
  live A p = Some n -> live A q = Some k -> p <> q -> (0 <= n)%Z -> (0 <= k)%Z ->
  (u p + n <= u q \/ u q + k <= u p)%Z.
Proof.
  intros C A m md p q n k CK HW Lp Lq NE Hn Hk.
  destruct (ai_live_disjoint A m (m_vmmaps md) p n q k (w_inv _ _ _ _ HW) Lp Lq NE) as [X|X];
    [left; pose proof (round16_ge n Hn); lia | right; pose proof (round16_ge k Hk); lia].
Qed.

Lemma zbv_ne : forall a b, (0 <= a < 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> a <> b -> Z_to_bv 64 a <> Z_to_bv 64 b.
Proof. intros a b Ha Hb NE E. apply NE. apply (f_equal bv_unsigned) in E. rewrite !u_Z2bv in E by lia. exact E. Qed.

Lemma pixobj_keep : forall C A A' M M' pix v cv, pixobj C A A' M pix v cv ->
  (forall x : word, (pix <= u x < pix + 64)%Z -> M' x = M x) ->
  (p_cmap v <> 0%Z -> forall x : word, (p_cmap v <= u x < p_cmap v + 24)%Z -> M' x = M x) ->
  pixobj C A A' M' pix v cv.
Proof.
  intros C A A' M M' pix v cv PO E1 E2. destruct PO as (PX & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & RC & RQ).
  split; [exact (PIXat_frame M M' pix v PX E1)|]. do 10 (split; [assumption|]). split; [|exact RQ].
  destruct RC as [Z0|(NZ & CM & REST)]; [left; exact Z0 | right]. split; [exact NZ|]. split; [|exact REST].
  apply (CMAPat_frame M M' _ _ CM). apply E2. lia.
Qed.

Ltac in_kept := unfold callee_kept; cbn [In]; repeat (first [left; reflexivity | right]).

Lemma payload_live : forall C A m md dp pl, Cok C -> W C A m md -> payload C dp pl -> (0 < Z.of_nat (length pl))%Z ->
  live A (Z_to_bv 64 dp) = Some (Z.of_nat (length pl)) /\ (4096 <= dp)%Z /\ (dp + Z.of_nat (length pl) <= alloc_top (c_vm C))%Z.
Proof.
  intros C A m md dp pl CK HW (L0 & B & Hdp & Hhi) Hn. pose proof (W_sub0 _ _ _ _ HW _ _ L0) as L. split; [exact L|].
  destruct (blk_range C A m md (Z_to_bv 64 dp) _ CK HW L Hn) as [G T]. rewrite u_Z2bv in G, T by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma pd_copy_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A5 M vm5 r (dp : Z) pl (nc w h d pixd data cm : Z) (cv : cmapv),
  Cok C -> DK C A m md regs s ret S kR bR ->
  aroom A5 vm5 (kR - RK_deser) (bR - RB_deser) -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  payload C dp pl ->
  (0 <= nc <= 256)%Z -> (4 * nc + 28 + 4 * (wpl_of w d * h) = Z.of_nat (length pl))%Z -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  W C A5 M (with_vmmaps vm5 md) -> POSTM C (c_A0 C) s m M ->
  pixobj C A A5 M pixd (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) cv ->
  (nc = 0 <-> cm = 0)%Z -> (cm <> 0%Z -> cmap_ok cv) ->
  cellsZ M (frame9 s ret (svr regs)) -> rdn SEGS M (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 10 = Z_to_bv 64 data -> getr r 11 = Z_to_bv 64 (dp + 4 * nc + 28) -> getr r 12 = Z_to_bv 64 (4 * (wpl_of w d * h)) ->
  getr r 1 = rl dVL_25134 0x25590 -> getr r 22 = Z_to_bv 64 nc -> getr r 9 = Z_to_bv 64 cm -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  realizes SEGS (mkCfg (mkst r (rl dF_1c9b4 0x1c9b4) M al_rom) (with_vmmaps vm5 md)) S.
Proof. rl_dbounds (dVLS_103ef :: dVL_25134 :: nil).
  intros C A m md regs s ret S kR bR A5 M vm5 r dp pl nc w h d pixd data cm cv CK HK Hrm Hrk Hrb Hs16 Hlo Hhi Hret H2 PLD Hnc Hsz HOK Hw Hh HW PM PO NCM CMOK CE Rp R2 RR R10 R11 R12 R1 R22 R9 H4.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct HOK as (DV & Hw2 & Hh2 & Hsz2). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  destruct (payload_live C A5 M _ dp pl CK HW PLD ltac:(lia)) as (Ldp & Gdp & Tdp).
  pose proof PLD as (Ldp0 & _ & Hdp1 & Hdphi).
  pose proof PO as (PX & _ & _ & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & RC & RQ). cbn [p_rc p_text p_wpl p_h p_data p_cmap] in Hn4, Ld, LdA, Ld0, NEdp, RC, RQ.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A5 M _ (Z_to_bv 64 pixd) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (wf_data _ WF) as Rdat. cbn [p_data] in Rdat.
  destruct (blk_range C A5 M _ (Z_to_bv 64 data) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  (* [comment removed for export] *)
  set (n := (4 * (wpl_of w d * h))%Z) in *. assert (En : n = (4 * (wpl_of w d * h))%Z) by reflexivity. clearbody n.
  set (bs := firstn (Z.to_nat n) (skipn (Z.to_nat (4 * nc + 28)) pl)).
  assert (Hlen : length bs = Z.to_nat n) by (subst bs; rewrite length_firstn, length_skipn; lia).
  pose proof (payload_at C A5 M _ dp pl HW PLD) as BAT.
  assert (Hsrc : rdn SEGS M (Z_to_bv 64 (dp + 4 * nc + 28)) (length bs) = Some bs).
  { rewrite Hlen. replace (dp + 4 * nc + 28)%Z with (dp + Z.of_nat (Z.to_nat (4 * nc + 28)))%Z by lia. subst bs.
    apply (bytes_at_field SEGS M dp pl); [lia | lia | lia | exact BAT]. }
  assert (Hdst : store_ok SEGS M (Z_to_bv 64 data) (length bs) = true).
  { rewrite Hlen, <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (M x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A5 M _ (Z_to_bv 64 data) _ x CK HW Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  assert (NEdd : Z_to_bv 64 data <> Z_to_bv 64 dp) by (intros E; rewrite E in Ld0; rewrite Ld0 in Ldp0; discriminate).
  pose proof (live_apart C A5 M _ _ _ _ _ CK HW Ld Ldp NEdd ltac:(lia) ltac:(lia)) as APd. rewrite !u_Z2bv in APd by lia.
  assert (HOKm : mcH M (Z_to_bv 64 data) (Z_to_bv 64 (dp + 4 * nc + 28)) n bs).
  { constructor; rewrite ?u_Z2bv by lia; [lia | exact Hlen | exact Hsrc | exact Hdst | lia | lia | lia]. }
  destruct (ref_memcpy M _ _ n bs al_rom HOKm r (rl dVL_25134 0x25590) ltac:(rl_ret_ok_VL) R1 R10 R11 R12) as (r6 & RUN6 & KP6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN6 |].
  set (M6 := wbytes M (Z_to_bv 64 data) bs) in *.
  assert (K2 : getr r6 2 = getr r 2) by (apply KP6; in_kept). assert (K9 : getr r6 9 = getr r 9) by (apply KP6; in_kept).
  assert (K22 : getr r6 22 = getr r 22) by (apply KP6; in_kept).
  assert (K24 : getr r6 24 = getr r 24) by (apply KP6; in_kept). assert (K25 : getr r6 25 = getr r 25) by (apply KP6; in_kept).
  assert (K3 : getr r6 3 = getr r 3) by (apply KP6; in_kept). assert (K4 : getr r6 4 = getr r 4) by (apply KP6; in_kept).
  assert (K26 : getr r6 26 = getr r 26) by (apply KP6; in_kept). assert (K27 : getr r6 27 = getr r 27) by (apply KP6; in_kept).
  assert (HW6 : W C A5 M6 (with_vmmaps vm5 md)).
  { subst M6. apply (W_store_blk C A5 M _ (Z_to_bv 64 data) (Z_to_bv 64 data) n bs CK HW Ld Ld0); rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
  assert (PM6 : POSTM C (c_A0 C) s m M6).
  { eapply POSTM_trans; [exact PM|]. subst M6. apply (POSTM_blk C (c_A0 C) A5 M _ (Z_to_bv 64 data) (Z_to_bv 64 data) n bs s CK HW Ld Ld0 (W_sub0 _ _ _ _ HW));
      rewrite ?u_Z2bv by lia; [lia | rewrite Hlen; lia]. }
  assert (OUT6 : forall x : word, ~ (data <= u x < data + n)%Z -> M6 x = M x).
  { intros x Hx. subst M6. apply wbytes_outside; rewrite Hlen, u_Z2bv by lia; lia. }
  assert (NEpd : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne; lia).
  pose proof (live_apart C A5 M _ _ _ _ _ CK HW Lp Ld NEpd ltac:(lia) ltac:(lia)) as APp. rewrite !u_Z2bv in APp by lia.
  assert (PO6 : pixobj C A A5 M6 pixd (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) cv).
  { apply (pixobj_keep C A A5 M M6 _ _ _ PO); cbn [p_cmap].
    - intros x Hx. apply OUT6. lia.
    - intros NZ x Hx. destruct RC as [Z0|(_ & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & NEca & NEcp & NEap & NEdc & NEda)]; [lia|].
      pose proof CM as (Hc0 & Hc64 & _).
      assert (NEcd : Z_to_bv 64 cm <> Z_to_bv 64 data) by (apply zbv_ne; lia).
      pose proof (live_apart C A5 M _ _ _ _ _ CK HW Lc Ld NEcd ltac:(lia) ltac:(lia)) as APc. rewrite !u_Z2bv in APc by lia.
      apply OUT6. lia. }
  assert (CE6 : cellsZ M6 (frame9 s ret (svr regs))) by (eapply (cells_out M M6 data (data + n)); [exact OUT6 | lia | lia | lia | exact CE]).
  assert (Rp6 : rdn SEGS M6 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
  { rewrite <- Rp. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. apply OUT6. cbn in Hx. lia. }
  assert (R2' : getr r6 2 = Z_to_bv 64 (s - 96)) by (rewrite K2; exact R2).
  destruct (Z.eq_dec nc 0) as [NC0|NC1].
  - (* [comment removed for export] *)
    assert (CM0 : cm = 0%Z) by (apply NCM; exact NC0).
    destruct (pd_L0 al_rom r6 M6 s pixd ltac:(lia) ltac:(lia) ltac:(lia) Rp6 R2' ltac:(rewrite K22, R22, NC0; reflexivity)) as (r7 & RUN7 & V10 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
    destruct (pd_RET al_rom r7 M6 s ret (svr regs) ltac:(lia) ltac:(lia) Hret (pd_cells_of _ _ _ _ CE6) ltac:(csr; reflexivity))
      as (r8 & RUN8 & U2 & U1 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN8 |].
    unfold svr in *.
    apply (HK A5 M6 vm5 r8 HW6).
    + apply cs_kept_intro; unfold pd_rest in RR; csr; reflexivity.
    + exact PM6.
    + right. exists pixd, (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data), cv. split; [csr; reflexivity | split; [exact PO6 | unfold pixfacts, hdr_ok; cbn [p_w p_h p_d p_cmap p_data]; rewrite <- ?En; exact (conj eq_refl (conj (conj DV (conj Hw2 (conj Hh2 Hsz2))) (conj Hw (conj Hh CMOK))))]].
    + room_tac.
  - (* [comment removed for export] *)
    assert (NZc : cm <> 0%Z) by (intros Z0; apply NC1; apply NCM; exact Z0).
    pose proof (CMOK NZc) as CMOK'.
    destruct RC as [Z0|(_ & CM & Lc & La & Hna & LcA & LaA & Lc0 & La0 & NEca & NEcp & NEap & NEdc & NEda)]; [lia|].
    pose proof PO6 as (PX6 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RC6 & _).
    destruct RC6 as [Z0|(_ & CM6 & _)]; [cbn [p_cmap] in Z0; lia|]. cbn [p_cmap] in CM6.
    destruct (pd_L1 al_rom r6 M6 s pixd nc cm ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rp6 R2' ltac:(rewrite K22; exact R22) ltac:(rewrite K9; exact R9))
      as (r7 & RUN7 & V10 & V11 & V12 & V1' & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
    apply (pixcmapIsValid_pix_W C A5 M6 _ r7 (s - 96) cm pixd (s - 76) cv (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) (rl dVL_25134 0x255a4) S
             CK HW6 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) ltac:(lia)
             ltac:(replace (s - 76)%Z with (s + (-76))%Z by lia; apply mod16_plus_mod4; [exact Hs16 | reflexivity])
             V1' ltac:(rl_ret_ok_VL) V10 V11 V12 CM6 CMOK' Lc PX6 Lp DV ltac:(cbn; lia) ltac:(cbn; lia) ltac:(reflexivity) ltac:(cbn [p_data p_wpl p_h]; rewrite <- En; exact Ld)).
    intros m7 r8 HW7 CS7 (valid & Hv & PV7 & A10).
    pose proof PV7 as [F7 L7]. pose proof CM as (Hc0 & Hc64 & _).
    destruct (blk_range C A5 M _ (Z_to_bv 64 cm) 24 CK HW Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    assert (PM7 : POSTM C (c_A0 C) s m m7).
    { eapply POSTM_trans; [exact PM6|].
      unshelve (eapply (POSTM_absorb C (c_A0 C) A5 M6 _ m7 s (s - 96) _ _ CK HW6 (W_sub0 _ _ _ _ HW6) ltac:(lia) _ _ Hhi PV7)); rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (Rv7 : rdn SEGS m7 (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 valid)).
    { rewrite (FRM_rdn16 C (s - 96) _ m7 (s - 76) 4 CK F7) by (cbn; lia). rewrite <- (w2l_Z4 valid) by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
    assert (Rp7 : rdn SEGS m7 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
    { rewrite (FRM_rdn16 C (s - 96) _ m7 (s - 96) 8 CK F7) by (cbn; lia). rewrite rdn_wbytes_out_Z; [exact Rp6 | rewrite length_N_to_le_bytes; lia]. }
    assert (CE7 : cellsZ m7 (frame9 s ret (svr regs))).
    { apply (cells_frm C (s - 96) (wbytes M6 (Z_to_bv 64 (s - 76)) (word_to_le_bytes 4 (Z_to_bv 64 valid))) m7 s ret _ CK F7 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      eapply (cells_out M6 _ (s - 76) (s - 72)); [intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE6]. }
    assert (EQb : forall (p k : Z) (x : word), live A5 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> m7 x = M6 x).
    { intros p k x L G0 TP Hx. pose proof (L7 (Z_to_bv 64 p) k (u x - p)%Z L ltac:(lia)) as E.
      replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
      rewrite E. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (PO7 : pixobj C A A5 m7 pixd (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) cv).
    { apply (pixobj_keep C A A5 M6 m7 _ _ _ PO6); cbn [p_cmap].
      - intros x Hx. exact (EQb pixd 64%Z x Lp ltac:(lia) TOPp Hx).
      - intros _ x Hx. exact (EQb cm 24%Z x Lc ltac:(lia) TOPc Hx). }
    assert (Y2 : getr r8 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    destruct Hv as [Val0|Val1].
    + (* [comment removed for export] *)
      subst valid.
      destruct (pd_M0 al_rom r8 m7 s ltac:(lia) ltac:(lia) Rv7 Y2) as (r9 & RUN9 & Z10 & Z1 & AG9).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN9 |].
      pose proof PO7 as (PX7 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RC7 & RQ7).
      destruct RC7 as [Z0|(_ & CM7 & _)]; [cbn [p_cmap] in Z0; lia|]. cbn [p_cmap] in CM7.
      apply (pixDestroy_W C A5 m7 _ r9 (s - 96) (s - 96) pixd cm (4 * c_nalloc cv) n (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) cv (rl dVL_25134 0x255bc) S
               CK HW7 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
               Z1 ltac:(rl_ret_ok_VL) ltac:(csr; reflexivity) ltac:(replace (s - 96)%Z with (s + (-96))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity]) Z10 ltac:(rewrite <- w2l_Z8 by lia; exact Rp7) PX7 eq_refl eq_refl eq_refl Lp Lp0).
      * right. cbn [p_data]. split; [exact Ld | split; [exact Ld0 | split; [lia | split; [exact NEdp | intros _; split; [exact NEdc | exact NEda]]]]].
      * right. split; [exact CM7 |]. split; [exact Lc|]. split; [exact La|]. split; [exact Lc0|]. split; [exact La0|]. split; [exact NEca|]. split; [exact NEcp|]. split; [exact NEap | exact Hna].
      * intros A6 m8 vm6 r10 HW8 CS8 PD8 PM8 R0 HRT6.
        rewrite with_vmmaps_twice in HW8 |- *.
        apply (pd_eptr_W C A m md regs s ret S kR bR A6 m8 vm6 r10 (0x255bc + dVL_25134) (0x103ef + dVLS_103ef) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW8).
        -- eapply POSTM_trans; [exact PM7 | eapply POSTM_mono; [| exact PM8]; lia].
        -- intros q. cbn [p_data] in PD8. destruct PD8 as (D1 & D2 & D3 & D4).
           destruct (bv_eq_dec _ q (Z_to_bv 64 pixd)) as [->|N1]; [rewrite D1, LpA; reflexivity|].
           destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [->|N2]; [rewrite (D2 ltac:(lia)), LdA; reflexivity|].
           destruct (bv_eq_dec _ q (Z_to_bv 64 cm)) as [->|N3]; [rewrite (proj1 (D3 NZc)), LcA; reflexivity|].
           destruct (bv_eq_dec _ q (Z_to_bv 64 (c_arr cv))) as [->|N4]; [rewrite (proj2 (D3 NZc)), LaA; reflexivity|].
           rewrite (D4 q N1 ltac:(intros _; exact N2) ltac:(intros _; split; [exact N3 | exact N4])). apply RQ; [exact N1 | exact N2 | intros _; split; [exact N3 | exact N4]].
        -- exact (cells_frm C (s - 96 + 8) m7 m8 s ret _ CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CE7).
        -- csr; reflexivity.
        -- unfold pd_rest in RR |- *. rest_solve.
        -- cbn. repeat (first [left; reflexivity | right]).
    + (* [comment removed for export] *)
      subst valid.
      destruct (pd_M1 al_rom r8 m7 s pixd ltac:(lia) ltac:(lia) ltac:(lia) Rv7 Rp7 Y2) as (r9 & RUN9 & Z10 & AG9).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN9 |].
      destruct (pd_RET al_rom r9 m7 s ret (svr regs) ltac:(lia) ltac:(lia) Hret (pd_cells_of _ _ _ _ CE7) ltac:(csr; reflexivity))
        as (r10 & RUN10 & U2 & U1 & U8 & U9 & U18 & U19 & U20 & U21 & U22 & U23 & AG10).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact RUN10 |].
      unfold svr in *.
      apply (HK A5 m7 vm5 r10 HW7).
      * apply cs_kept_intro; unfold pd_rest in RR; csr; reflexivity.
      * exact PM7.
      * right. exists pixd, (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data), cv. split; [csr; reflexivity | split; [exact PO7 | unfold pixfacts, hdr_ok; cbn [p_w p_h p_d p_cmap p_data]; rewrite <- ?En; exact (conj eq_refl (conj (conj DV (conj Hw2 (conj Hh2 Hsz2))) (conj Hw (conj Hh CMOK))))]].
      * room_tac.
Qed.

(* [comment removed for export] *)
Lemma LIVK_rd : forall C A M M' md (p k : Z) (x : word), Cok C -> W C A M md -> LIVK A M M' ->
  live A (Z_to_bv 64 p) = Some k -> (0 <= p)%Z -> (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> M' x = M x.
Proof.
  intros C A M M' md p k x CK HW L Lp G0 TP Hx. pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof (L (Z_to_bv 64 p) k (u x - p)%Z Lp ltac:(lia)) as E.
  replace (at_ (Z_to_bv 64 p) (u x - p)) with x in E by (unfold at_; apply bv_eq; rewrite !u_Z2bv; rewrite ?u_Z2bv; pose proof (u64_range x); lia).
  exact E.
Qed.

Definition pixv0 (w h d cm data : Z) : pixv := PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data.

(* [comment removed for export] *)
Lemma pd_created_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A3 M vm3 r (dp : Z) pl (nc w h d pixd data : Z),
  Cok C -> DK C A m md regs s ret S kR bR ->
  aroom A3 vm3 (kR - (RK_hdr + RK_pix)) (bR - (RB_hdr + RB_pix)) -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  payload C dp pl ->
  (0 <= nc <= 256)%Z -> (4 * nc + 28 + 4 * (wpl_of w d * h) = Z.of_nat (length pl))%Z -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  W C A3 M (with_vmmaps vm3 md) -> POSTM C (c_A0 C) s m M ->
  pixobj C A A3 M pixd (pixv0 w h d 0 data) cmap0 ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 10 = Z_to_bv 64 pixd -> getr r 22 = Z_to_bv 64 nc -> getr r 23 = Z_to_bv 64 dp ->
  getr r 8 = Z_to_bv 64 (4 * (wpl_of w d * h)) -> (dp mod 4 = 0)%Z ->
  realizes SEGS (mkCfg (mkst r (rl dVL_25134 0x25400) M al_rom) (with_vmmaps vm3 md)) S.
Proof. rl_dbounds (dVLS_10a7c :: dVL_25134 :: nil).
  intros C A m md regs s ret S kR bR A3 M vm3 r dp pl nc w h d pixd data CK HK Hrm Hrk Hrb Hs16 Hlo Hhi Hret H2 H4 PLD Hnc Hsz HOK Hw Hh HW PM PO CE R2 RR R10 R22 R23 R8 ALd.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz2). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PLD as (Ldp0 & _ & Hdp1 & Hdphi).
  pose proof PO as (PX & _ & _ & Hn4 & Lp & LpA & Lp0 & Ld & LdA & Ld0 & NEdp & _ & RQ). cbn [p_rc p_text p_wpl p_h p_data p_cmap pixv0] in Hn4, Ld, LdA, Ld0, NEdp, RQ.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat. cbn [p_data pixv0] in Rdat.
  destruct (blk_range C A3 M _ (Z_to_bv 64 pixd) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A3 M _ (Z_to_bv 64 data) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A3 M _ _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia.
  assert (ALp8 : (pixd mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pixd); apply mod16_plus_mod8; [exact ALp16 | reflexivity]).
  pose proof (ai_live_hull A3 M _ _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd16 & _). rewrite u_Z2bv in ALd16 by lia.
  assert (ALdat : (data mod 4 = 0)%Z) by (rewrite <- (Z.add_0_r data); apply mod16_plus_mod4; [exact ALd16 | reflexivity]).
  set (n := (4 * (wpl_of w d * h))%Z) in *. assert (En : n = (4 * (wpl_of w d * h))%Z) by reflexivity. clearbody n.
  pose proof (W_sok_win C A3 M _ (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  set (M' := wbytes M (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
  assert (WP' : W C A3 M' (with_vmmaps vm3 md) /\ POSTM C (c_A0 C) s m M').
  { subst M'. apply (WP_win C A3 (c_A0 C) m M _ _ _ s CK (conj HW PM) (W_sub0 _ _ _ _ HW)); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
  destruct WP' as [HW' PM'].
  assert (OUT' : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> M' x = M x).
  { intros x Hx. subst M'. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
  assert (PO' : pixobj C A A3 M' pixd (pixv0 w h d 0 data) cmap0).
  { apply (pixobj_keep C A A3 M M' _ _ _ PO); [intros x Hx; apply OUT'; lia | cbn [p_cmap pixv0]; lia]. }
  assert (CE' : cellsZ M' (frame9 s ret (svr regs))) by (eapply (cells_out M M' (s - 96) (s - 88)); [exact OUT' | lia | lia | lia | exact CE]).
  assert (Rp' : rdn SEGS M' (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
  { subst M'. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  pose proof PO' as (PX' & _).
  destruct (Z.eq_dec nc 0) as [NC0|NC1].
  - (* [comment removed for export] *)
    destruct (pd_I1 al_rom r M s pixd ltac:(lia) ltac:(lia) SOK ltac:(lia) R2 R10 ltac:(rewrite R22, NC0; reflexivity)) as (r1 & RUN1 & Q9 & Q18 & Q10 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. fold M'.
    destruct (pd_GD al_rom r1 M' pixd dp nc n _ PX' Gp ALp8 Hnc ltac:(lia) ltac:(lia) ALd ALdat Q10 ltac:(csr; reflexivity) ltac:(rewrite Q18, NC0; reflexivity) ltac:(csr; reflexivity))
      as (r2 & RUN2 & V10 & V11 & V12 & V1 & V18 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |].
    cbn [p_data pixv0] in V10.
    apply (pd_copy_W C A m md regs s ret S kR bR A3 M' vm3 r2 dp pl nc w h d pixd data 0 cmap0 CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 PLD Hnc ltac:(lia) HOK Hw Hh HW' PM' PO'
             ltac:(lia) ltac:(lia) CE' Rp' ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR |- *; rest_solve) V10 V11 ltac:(rewrite V12, En; reflexivity) V1
             ltac:(csr; rewrite NC0; reflexivity) ltac:(csr; reflexivity) H4).
  - (* [comment removed for export] *)
    destruct (pd_I2 al_rom r M s pixd dp nc ltac:(lia) ltac:(lia) SOK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) R2 R10 R22 R23) as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & Q18 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. fold M'.
    apply (pixcmapDeserialize_W C A3 M' _ r1 (s - 96) (dp + 24) nc (Z_to_bv 64 dp) (Z.of_nat (length pl)) (rl dVL_25134 0x25428) S CK HW'
             ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(rl_ret_ok_VL)
             ltac:(csr; reflexivity) Q10 Q11 Q12 ltac:(lia) Ldp0 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)
             (kR - (RK_hdr + RK_pix)) (bR - (RB_hdr + RB_pix)) ltac:(room_tac) ltac:(room_consts; lia) ltac:(room_consts; lia)).
    intros A4 m4 vm4 r4 HW4 CS4 PM4 RES4 Hrm4. rewrite with_vmmaps_twice in HW4 |- *.
    pose proof PM4 as [F4 L4].
    assert (PM4' : POSTM C (c_A0 C) s m m4).
    { eapply POSTM_trans; [exact PM'|]. apply (POSTM_sub C (c_A0 C) A3); [exact (W_sub0 _ _ _ _ HW')|]. eapply POSTM_mono; [|exact PM4]. lia. }
    assert (CE4 : cellsZ m4 (frame9 s ret (svr regs))) by (exact (cells_frm C (s - 96) M' m4 s ret _ CK F4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CE')).
    assert (Rp4 : rdn SEGS m4 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
    { rewrite (FRM_rdn16 C (s - 96) M' m4 (s - 96) 8 CK F4) by (cbn; lia). exact Rp'. }
    assert (PO4 : pixobj C A A3 m4 pixd (pixv0 w h d 0 data) cmap0).
    { apply (pixobj_keep C A A3 M' m4 _ _ _ PO'); [| cbn [p_cmap pixv0]; lia]. intros x Hx. exact (LIVK_rd C A3 M' m4 _ pixd 64 x CK HW' L4 Lp ltac:(lia) TOPp Hx). }
    pose proof PO4 as (PX4 & _).
    assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    destruct RES4 as [[A40 LQ4] | (cm & arr & A4cm & CN)].
    + (* [comment removed for export] *)
      destruct (pd_J0 al_rom r4 m4 s ltac:(lia) ltac:(lia) Y2 A40) as (r5 & RUN5 & Z10 & Z1 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
      assert (Ld4 : live A4 (Z_to_bv 64 data) = Some n) by (rewrite LQ4; exact Ld).
      apply (pixDestroy_W C A4 m4 _ r5 (s - 96) (s - 96) pixd 0 0 n (pixv0 w h d 0 data) cmap0 (rl dVL_25134 0x25530) S
               CK HW4 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
               Z1 ltac:(rl_ret_ok_VL) ltac:(csr; reflexivity) ltac:(replace (s - 96)%Z with (s + (-96))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity])
               Z10 ltac:(rewrite <- w2l_Z8 by lia; exact Rp4) PX4 eq_refl eq_refl eq_refl
               ltac:(rewrite LQ4; exact Lp) Lp0).
      * right. cbn [p_data pixv0]. split; [exact Ld4 | split; [exact Ld0 | split; [lia | split; [exact NEdp | intros X; exfalso; exact (X eq_refl)]]]].
      * left. reflexivity.
      * intros A5 m5 vm5 r6 HW5 CS5 PD5 PM5 R0 HRT5. rewrite with_vmmaps_twice in HW5 |- *.
        apply (pd_eptr_W C A m md regs s ret S kR bR A5 m5 vm5 r6 (0x25530 + dVL_25134) (0x10a7c + dVLS_10a7c) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW5).
        -- eapply POSTM_trans; [exact PM4' | eapply POSTM_mono; [| exact PM5]; lia].
        -- intros q. cbn [p_data pixv0] in PD5. destruct PD5 as (D1 & D2 & D3 & D4).
           destruct (bv_eq_dec _ q (Z_to_bv 64 pixd)) as [->|N1]; [rewrite D1, LpA; reflexivity|].
           destruct (bv_eq_dec _ q (Z_to_bv 64 data)) as [->|N2]; [rewrite (D2 ltac:(lia)), LdA; reflexivity|].
           rewrite (D4 q N1 ltac:(intros _; exact N2) ltac:(intros X; exfalso; exact (X eq_refl))), LQ4. apply RQ; [exact N1 | exact N2 | intros X; exfalso; exact (X eq_refl)].
        -- exact (cells_frm C (s - 96 + 8) m4 m5 s ret _ CK (proj1 PM5) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CE4).
        -- csr; reflexivity.
        -- unfold pd_rest in RR |- *. rest_solve.
        -- cbn. right. left. reflexivity.
    + (* [comment removed for export] *)
      destruct CN as (Gc & TOPc & ALc & Ga & TOPa & ALa & NEca & Lc3 & La3 & Lc0 & La0 & Lc & La & LQ4 & CM4).
      set (cv := CMAPV arr (cdepth nc) (2 ^ cdepth nc) nc 0) in CM4.
      pose proof (cdepth_cases nc) as Hcd. pose proof (cdepth_fits nc ltac:(lia)) as [Hfit Hpow].
      assert (NEpc : Z_to_bv 64 pixd <> Z_to_bv 64 cm) by (intros E; rewrite E in Lp; rewrite Lp in Lc3; discriminate).
      assert (NEpa : Z_to_bv 64 pixd <> Z_to_bv 64 arr) by (intros E; rewrite E in Lp; rewrite Lp in La3; discriminate).
      assert (NEdc : Z_to_bv 64 data <> Z_to_bv 64 cm) by (intros E; rewrite E in Ld; rewrite Ld in Lc3; discriminate).
      assert (NEda : Z_to_bv 64 data <> Z_to_bv 64 arr) by (intros E; rewrite E in Ld; rewrite Ld in La3; discriminate).
      assert (Lp4 : live A4 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (LQ4 _ NEpc NEpa); exact Lp).
      assert (Ld4 : live A4 (Z_to_bv 64 data) = Some n) by (rewrite (LQ4 _ NEdc NEda); exact Ld).
      assert (CMOK : cmap_ok cv) by (subst cv; unfold cmap_ok; cbn [c_d c_nalloc c_n c_arr]; split; [exact Hcd | split; [reflexivity | split; lia]]).
      destruct (pd_J1 al_rom r4 m4 s cm pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Rp4 Y2 A4cm) as (r5 & RUN5 & Z10 & Z11 & Z9 & Z1 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
      apply (pixSetColormap_W C (c_A0 C) A4 m4 _ r5 (s - 96) pixd cm (pixv0 w h d 0 data) cv (rl dVL_25134 0x2543c) S CK HW4 (W_sub0 _ _ _ _ HW4)
               ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) Z1 ltac:(rl_ret_ok_VL)
               Z10 Z11 PX4 eq_refl Lp4 Lp0 Lp0 CM4 CMOK Lc NEpc).
      intros m5 r6 HW5 CS5 PM5 PX5 CM5 A60.
      pose proof PM5 as [F5 L5].
      assert (PM5' : POSTM C (c_A0 C) s m m5) by (eapply POSTM_trans; [exact PM4' | eapply POSTM_mono; [| exact PM5]; lia]).
      assert (CE5 : cellsZ m5 (frame9 s ret (svr regs))) by (exact (cells_frm C (s - 96) m4 m5 s ret _ CK F5 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CE4)).
      assert (Rp5 : rdn SEGS m5 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
      { rewrite (FRM_rdn16 C (s - 96) m4 m5 (s - 96) 8 CK F5) by (cbn; lia). exact Rp4. }
      cbn [set_cmap pixv0 p_w p_h p_d p_spp p_wpl p_rc p_xres p_yres p_fmt p_spec p_text p_data] in PX5.
      assert (PO5 : pixobj C A A4 m5 pixd (pixv0 w h d cm data) cv).
      { unfold pixobj, pixv0. cbn [p_rc p_text p_wpl p_h p_data p_cmap]. subst cv. cbn [c_arr c_nalloc]. rewrite <- En.
        split; [exact PX5|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
        split; [exact Lp4|]. split; [exact LpA|]. split; [exact Lp0|]. split; [exact Ld4|]. split; [exact LdA|]. split; [exact Ld0|]. split; [exact NEdp|].
        split.
        - right. split; [lia|]. split; [exact CM5|]. split; [exact Lc|]. split; [exact La|]. split; [lia|].
          split; [rewrite <- (RQ _ ltac:(intros E; apply NEpc; symmetry; exact E) ltac:(intros E; apply NEdc; symmetry; exact E) ltac:(intros X; exfalso; exact (X eq_refl))); exact Lc3|].
          split; [rewrite <- (RQ _ ltac:(intros E; apply NEpa; symmetry; exact E) ltac:(intros E; apply NEda; symmetry; exact E) ltac:(intros X; exfalso; exact (X eq_refl))); exact La3|].
          split; [exact Lc0|]. split; [exact La0|]. split; [exact NEca|].
          split; [intros E; apply NEpc; rewrite E; reflexivity|]. split; [intros E; apply NEpa; rewrite E; reflexivity|].
          split; [intros E; apply NEdc; rewrite E; reflexivity | intros E; apply NEda; rewrite E; reflexivity].
        - intros q N1 N2 N34. destruct (N34 ltac:(lia)) as [N3 N4]. rewrite (LQ4 q N3 N4). apply RQ; [exact N1 | exact N2 | intros X; exfalso; exact (X eq_refl)]. }
      destruct (pd_K al_rom r6 m5 s pixd ltac:(lia) ltac:(lia) ltac:(lia) Rp5 ltac:(csr; reflexivity) A60) as (r7 & RUN7 & V10 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
      destruct (pd_GD al_rom r7 m5 pixd dp nc n _ PX5 Gp ALp8 Hnc ltac:(lia) ltac:(lia) ALd ALdat V10 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (r8 & RUN8 & U10 & U11 & U12 & U1 & U18 & AG8).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN8 |].
      cbn [p_data] in U10.
      apply (pd_copy_W C A m md regs s ret S kR bR A4 m5 vm4 r8 dp pl nc w h d pixd data cm cv CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 PLD Hnc ltac:(lia) HOK Hw Hh HW5 PM5' PO5
               ltac:(lia) ltac:(intros _; exact CMOK) CE5 Rp5 ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR |- *; rest_solve) U10 U11 ltac:(rewrite U12, En; reflexivity) U1
               ltac:(csr; reflexivity) ltac:(csr; reflexivity) H4).
Qed.


(* [comment removed for export] *)
Lemma pd_hdr_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (dp : Z) pl (nc wr hr dr ir : Z),
  Cok C -> DK C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_hdr) (bR - RB_hdr) -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  payload C dp pl -> let nb := Z.of_nat (length pl) in
  (28 <= nb < 2 ^ 26)%Z -> (0 <= nc <= 256)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z -> (0 <= dr < 2 ^ 32)%Z ->
  bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * nc + 24)) pl)) = ir ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 22 = Z_to_bv 64 nc -> getr r 20 = Z_to_bv 64 nb -> getr r 23 = Z_to_bv 64 dp -> getr r 18 = Z_to_bv 64 hr -> getr r 9 = Z_to_bv 64 wr ->
  getr r 19 = Z_to_bv 64 (zx (sw32 dr)) -> (dp mod 4 = 0)%Z ->
  ((getr r 10 = Z_to_bv 64 0 /\ forall q, live A1 q = live A q)
   \/ (exists jpegiostub, getr r 10 = Z_to_bv 64 jpegiostub /\ (hdr_ok wr hr (zx (sw32 dr)) /\ pix_new C A A1 M jpegiostub (pix_hdr wr hr (zx (sw32 dr)))))) ->
  realizes SEGS (mkCfg (mkst r (rl dVL_25134 0x25394) M al_rom) (with_vmmaps vm1 md)) S.
Proof. rl_dbounds (dVLS_10488 :: dVLS_104ff :: dVLS_10807 :: dVL_25134 :: nil).
  intros C A m md regs s ret S kR bR A1 M vm1 r dp pl nc wr hr dr ir CK HK Hrm Hrk Hrb Hs16 Hlo Hhi Hret H2 H4 PLD nb Hnb Hnc Hnc4 Hwr Hhr Hwh Hdr Hir HW PM CE R2 RR R22 R20 R23 R18 R9 R19 ALd RES.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  pose proof PLD as (Ldp0 & _ & Hdp1 & Hdphi). fold nb in Hdphi.
  destruct (payload_live C A1 M _ dp pl CK HW PLD ltac:(lia)) as (Ldp & Gdp & Tdp). fold nb in Ldp, Tdp.
  pose proof (W_sok_win C A1 M _ (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  set (d := zx (sw32 dr)) in *. pose proof (zx_range (sw32 dr)) as Hd64. fold d in Hd64.
  pose proof (zx_range (sw32 ir)) as Hir64.
  destruct RES as [[A0 LQ] | (jpegiostub & A1p & HOK & PN)].
  - (* [comment removed for export] *)
    destruct (pd_G0 al_rom r M s ltac:(lia) ltac:(lia) SOK R2 A0) as (r1 & RUN1 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M' := wbytes M _ _).
    assert (WP' : W C A1 M' (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) s m M').
    { subst M'. apply (WP_win C A1 (c_A0 C) m M _ _ _ s CK (conj HW PM) (W_sub0 _ _ _ _ HW)); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
    destruct WP' as [HW' PM'].
    assert (CE' : cellsZ M' (frame9 s ret (svr regs))).
    { eapply (cells_out M M' (s - 88) (s - 80)); [intros x Hx; subst M'; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE]. }
    apply (pd_tail_W C A m md regs s ret S kR bR A1 M' vm1 r1 (0x25498 + dVL_25134) (0x10488 + dVLS_10488) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW' PM' LQ CE' ltac:(csr; reflexivity)
             ltac:(unfold pd_rest in RR |- *; rest_solve)). cbn. repeat (first [left; reflexivity | right]).
  - (* [comment removed for export] *)
    destruct HOK as (DV & Hw2 & Hh2 & Hsz2). pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range wr d ltac:(lia) DV) as Hwpl.
    destruct PN as (Gp1 & TOPp1 & ALp1 & LAp1 & L0p1 & L1p1 & LQ1 & PX1).
    assert (ALp8 : (jpegiostub mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r jpegiostub); apply mod16_plus_mod8; [exact ALp1 | reflexivity]).
    pose proof (payload_at C A1 M _ dp pl HW PLD) as BAT.
    destruct (payload_field M dp pl (Z.to_nat (4 * nc + 24)) BAT ltac:(lia) ltac:(lia) ltac:(lia)) as [Ri Bir].
    replace (dp + Z.of_nat (Z.to_nat (4 * nc + 24)))%Z with (dp + 4 * nc + 24)%Z in Ri by lia.
    destruct (pd_G al_rom r M s dp nb nc jpegiostub (wpl_of wr d) hr ir (pix_hdr wr hr d) _ ltac:(lia) ltac:(lia) SOK PX1 Gp1 ltac:(lia) ALp8 eq_refl Hhr ltac:(lia) Hsz2
                Hnc ltac:(lia) Hnc4 ltac:(lia) ltac:(lia) ALd Ri Hir ltac:(lia) R2 A1p R22 R20 R23 R18)
      as (r1 & RUN1 & Q2 & Q10 & Q1 & Q20 & Q8 & Q21 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    set (M1 := wbytes M _ _).
    assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) s m M1).
    { subst M1. apply (WP_win C A1 (c_A0 C) m M _ _ _ s CK (conj HW PM) (W_sub0 _ _ _ _ HW)); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
    destruct WP1 as [HW1 PM1].
    assert (OUT1 : forall x : word, ~ (s - 88 <= u x < s - 80)%Z -> M1 x = M x).
    { intros x Hx. subst M1. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
    assert (CE1 : cellsZ M1 (frame9 s ret (svr regs))) by (eapply (cells_out M M1 (s - 88) (s - 80)); [exact OUT1 | lia | lia | lia | exact CE]).
    assert (PX1' : PIXat M1 jpegiostub (pix_hdr wr hr d)) by (apply (PIXat_frame M M1 _ _ PX1); intros x Hx; apply OUT1; lia).
    assert (Rpp : rdn SEGS M1 (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 jpegiostub)).
    { subst M1. rewrite <- w2l_Z8 by lia. apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
    apply (pixDestroy_W C A1 M1 _ r1 (s - 96) (s - 88) jpegiostub 0 0 0 (pix_hdr wr hr d) cmap0 (rl dVL_25134 0x253e8) S
             CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
             Q1 ltac:(rl_ret_ok_VL) ltac:(csr; reflexivity) ltac:(replace (s - 88)%Z with (s + (-88))%Z by lia; apply mod16_plus_mod8; [exact Hs16 | reflexivity])
             Q10 Rpp PX1' eq_refl eq_refl eq_refl L1p1 L0p1).
    { left. reflexivity. }
    { left. reflexivity. }
    intros A2 m2 vm2 r2 HW2 CS2 PD2 PM2 R0 HRT2. rewrite with_vmmaps_twice in HW2 |- *.
    assert (LQ2 : forall q, live A2 q = live A q).
    { intros q. destruct PD2 as (D1 & _ & _ & D4). destruct (bv_eq_dec _ q (Z_to_bv 64 jpegiostub)) as [->|N1]; [rewrite D1, LAp1; reflexivity|].
      rewrite (D4 q N1 ltac:(intros X; exfalso; exact (X eq_refl)) ltac:(intros X; exfalso; exact (X eq_refl))). apply LQ1. exact N1. }
    assert (PM2' : POSTM C (c_A0 C) s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM2]; lia]).
    assert (CE2 : cellsZ m2 (frame9 s ret (svr regs))) by (exact (cells_frm C (s - 88 + 8) M1 m2 s ret _ CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CE1)).
    assert (Y2 : getr r2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    destruct (Z.eq_dec (4 * (wpl_of wr d * hr)) (nb - 4 * nc - 28)) as [E1|N1]; [destruct (Z.eq_dec (4 * (wpl_of wr d * hr)) (zx (sw32 ir))) as [E2|N2]|].
    + (* [comment removed for export] *)
      destruct (pd_H al_rom r2 m2 (4 * (wpl_of wr d * hr)) wr hr d ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; f_equal; lia) ltac:(csr; f_equal; lia)
                  ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r3 & RUN3 & V10 & V11 & V12 & V1 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
      apply (pixCreate_W C A2 m2 _ r3 (s - 96) wr hr d (rl dVL_25134 0x25400) S CK HW2 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
               ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(rl_ret_ok_VL) ltac:(csr; reflexivity) V10 V11 V12 Hwr Hhr Hwh ltac:(lia)).
      intros A3 m3 vm3 r4 HW3 CS3 PM3 RES3 HRT3. rewrite with_vmmaps_twice in HW3 |- *.
      pose proof PM3 as [F3 L3].
      assert (PM3' : POSTM C (c_A0 C) s m m3).
      { eapply POSTM_trans; [exact PM2'|]. apply (POSTM_sub C (c_A0 C) A2); [exact (W_sub0 _ _ _ _ HW2)|]. eapply POSTM_mono; [|exact PM3]. lia. }
      assert (CE3 : cellsZ m3 (frame9 s ret (svr regs))) by (exact (cells_frm C (s - 96) m2 m3 s ret _ CK F3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CE2)).
      assert (Y3 : getr r4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      destruct RES3 as [[A40 LQ3] | (pixd & data & A4p & _ & PR)].
      * (* [comment removed for export] *)
        pose proof (W_sok_win C A3 m3 _ (s - 96) 96 CK HW3 ltac:(lia) ltac:(cbn; lia)) as SOK3.
        destruct (pd_I0 al_rom r4 m3 s ltac:(lia) ltac:(lia) SOK3 Y3 A40) as (r5 & RUN5 & AG5).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
        set (M' := wbytes m3 _ _).
        assert (WP' : W C A3 M' (with_vmmaps vm3 md) /\ POSTM C (c_A0 C) s m M').
        { subst M'. apply (WP_win C A3 (c_A0 C) m m3 _ _ _ s CK (conj HW3 PM3') (W_sub0 _ _ _ _ HW3)); rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
        destruct WP' as [HW' PM'].
        assert (CE' : cellsZ M' (frame9 s ret (svr regs))).
        { eapply (cells_out m3 M' (s - 96) (s - 88)); [intros x Hx; subst M'; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia | lia | lia | exact CE3]. }
        apply (pd_eptr_W C A m md regs s ret S kR bR A3 M' vm3 r5 (0x254f8 + dVL_25134) (0x10807 + dVLS_10807) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW' PM').
        -- intros q. rewrite LQ3. apply LQ2.
        -- exact CE'.
        -- csr; reflexivity.
        -- unfold pd_rest in RR |- *; rest_solve.
        -- cbn. left. reflexivity.
      * (* [comment removed for export] *)
        destruct PR as (Gp & TOPp & ALp & Gd & TOPd & ALdd & NEpd & L2p & L2d & L0p & L0d & L3p & L3d & LQ3 & PX3 & _).
        cbn [p_wpl p_h set_data pix_hdr] in TOPd, L3d.
        apply (pd_created_W C A m md regs s ret S kR bR A3 m3 vm3 r4 dp pl nc wr hr d pixd data CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 H4 PLD Hnc ltac:(lia)
                 (conj DV (conj Hw2 (conj Hh2 Hsz2))) ltac:(lia) ltac:(lia) HW3 PM3').
        -- unfold pixobj, pixv0. cbn [p_rc p_text p_wpl p_h p_data p_cmap].
           split; [exact PX3|]. split; [reflexivity|]. split; [reflexivity|]. split; [lia|].
           split; [exact L3p|]. split; [rewrite <- LQ2; exact L2p|]. split; [exact L0p|]. split; [exact L3d|]. split; [rewrite <- LQ2; exact L2d|]. split; [exact L0d|].
           split; [intros E; apply NEpd; symmetry; exact E|]. split; [left; reflexivity|].
           intros q N1' N2' _. rewrite (LQ3 q N1' N2'). apply LQ2.
        -- exact CE3.
        -- exact Y3.
        -- unfold pd_rest in RR |- *; rest_solve.
        -- exact A4p.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- csr; reflexivity.
        -- exact ALd.
    + (* [comment removed for export] *)
      destruct (pd_Hbad al_rom r2 m2 (4 * (wpl_of wr d * hr)) (nb - 4 * nc - 28) (zx (sw32 ir)) ltac:(lia) ltac:(lia) Hir64 ltac:(right; exact N2)
                  (W_sev_got C A2 m2 _ HW2) (W_sev C A2 m2 _ HW2) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r3 & RUN3 & V10 & V11 & V1 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
      apply (pd_lerr_W C A m md regs s ret S kR bR A2 m2 vm2 r3 (0x104ff + dVLS_104ff) (0x254f4 + dVL_25134) 83 CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW2 PM2' LQ2 CE2 ltac:(csr; reflexivity)
               ltac:(unfold pd_rest in RR |- *; rest_solve) V10 V11 V1 ltac:(right; reflexivity) ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right])) str_e8).
    + (* [comment removed for export] *)
      destruct (pd_Hbad al_rom r2 m2 (4 * (wpl_of wr d * hr)) (nb - 4 * nc - 28) (zx (sw32 ir)) ltac:(lia) ltac:(lia) Hir64 ltac:(left; exact N1)
                  (W_sev_got C A2 m2 _ HW2) (W_sev C A2 m2 _ HW2) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r3 & RUN3 & V10 & V11 & V1 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
      apply (pd_lerr_W C A m md regs s ret S kR bR A2 m2 vm2 r3 (0x104ff + dVLS_104ff) (0x254f4 + dVL_25134) 83 CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW2 PM2' LQ2 CE2 ltac:(csr; reflexivity)
               ltac:(unfold pd_rest in RR |- *; rest_solve) V10 V11 V1 ltac:(right; reflexivity) ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right])) str_e8).
Qed.

Theorem pixDeserialize_W : forall C A m md regs (s dp : Z) (pl : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = rl dA_2f6b0 0x2f7b8 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  (1 <= dp < 2 ^ 64)%Z -> (Z.of_nat (length pl) < 2 ^ 26)%Z -> (28 <= Z.of_nat (length pl) -> payload C dp pl)%Z -> (dp mod 4 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_deser <= kR)%Z -> (RB_deser <= bR)%Z ->
  DK C A m md regs s ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (rl dVL_25134 0x25134) m al_rom) md) S.
Proof. rl_dbounds (dVLS_10322 :: dVLS_1034c :: dVLS_10726 :: dVLS_10749 :: dVLS_1079f :: dVLS_1097f :: dVL_25134 :: nil).
  intros C A m md regs s dp pl ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hdp64 Hnb HPL Hal4 kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLG] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  set (nb := Z.of_nat (length pl)) in *.
  pose proof (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pd_A0 al_rom regs m s dp nb ret ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11) as (r0 & RUN0 & P2 & P10 & P11 & P12 & P13 & AG0).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN0 |].
  assert (WP0 : W C A (FR9 m s ret regs) md /\ POSTM C (c_A0 C) s m (FR9 m s ret regs)).
  { unfold FR9. apply (WP_win C A (c_A0 C) m _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HW) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
    do 7 (apply (WP_win C A (c_A0 C) m _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HW) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia]).
    apply (WP_win C A (c_A0 C) m _ _ _ _ s CK); [| exact (W_sub0 _ _ _ _ HW) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
    split; [exact HW | apply POSTM_refl]. }
  destruct WP0 as [HW0 PM0]. set (M0 := FR9 m s ret regs) in *.
  pose proof (cells_FR9 m s ret regs ltac:(lia) ltac:(lia)) as CE0. fold M0 in CE0.
  assert (RR0 : forall x, In x pd_rest -> getr r0 x = getr regs x) by (unfold pd_rest; rest_solve).
  rewrite <- (with_vmmaps_same md) in HW0 |- *.
  destruct (Z_lt_ge_dec nb 28) as [SMALL|BIG].
  { (* [comment removed for export] *)
    destruct (pd_A2 al_rom r0 M0 nb ltac:(lia) P12 P13 P11 (W_sev_got C A M0 _ HW0) (W_sev C A M0 _ HW0)) as (r1 & RUN1 & Q10 & Q11 & Q12 & Q1 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
    apply (pd_lerr_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) r1 (0x10726 + dVLS_10726) (0x251a0 + dVL_25134) 34 CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW0 PM0 ltac:(intros; reflexivity) CE0
             ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR0 |- *; rest_solve) Q10 Q11 Q1 ltac:(left; reflexivity)
             ltac:(apply fmts1_16; cbn; repeat (first [left; reflexivity | right])) str_e1). }
  pose proof (HPL ltac:(lia)) as PLD.
  pose proof PLD as (Ldp0 & _ & Hdp1 & Hdphi). fold nb in Hdphi.
  destruct (payload_live C A m md dp pl CK HW PLD ltac:(lia)) as (Ldp & Gdp & Tdp). fold nb in Ldp, Tdp.
  destruct (pd_A1 al_rom r0 M0 nb ltac:(lia) P12 P13) as (r1 & RUN1 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
  assert (RR1 : forall x, In x pd_rest -> getr r1 x = getr regs x) by (unfold pd_rest; rest_solve).
  assert (P10' : getr r1 10 = Z_to_bv 64 dp) by (csr; reflexivity).
  pose proof (payload_at C A M0 _ dp pl HW0 PLD) as BAT.
  (* [comment removed for export] *)
  pose proof (payload_byte M0 dp pl 0 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as Rb0. rewrite Z.add_0_r in Rb0.
  pose proof (payload_byte M0 dp pl 1 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as Rb1.
  pose proof (payload_byte M0 dp pl 2 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as Rb2.
  pose proof (payload_byte M0 dp pl 3 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as Rb3.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Rb1, Rb2, Rb3.
  set (b0 := nth 0 pl (Z_to_bv 8 0)) in Rb0. set (b1 := nth 1 pl (Z_to_bv 8 0)) in Rb1. set (b2 := nth 2 pl (Z_to_bv 8 0)) in Rb2. set (b3 := nth 3 pl (Z_to_bv 8 0)) in Rb3.
  assert (MAGIC : {(u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z} + {~ (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z}).
  { destruct (Z.eq_dec (u b0) 115); [|right; lia]. destruct (Z.eq_dec (u b1) 112); [|right; lia]. destruct (Z.eq_dec (u b2) 105); [|right; lia]. destruct (Z.eq_dec (u b3) 120); [|right; lia]. left; lia. }
  destruct MAGIC as [(E0 & E1 & E2 & E3) | NM].
  2: { destruct (pd_Bbad al_rom r1 M0 dp b0 b1 b2 b3 ltac:(lia) ltac:(lia) Rb0 Rb1 Rb2 Rb3 NM P10') as (r2 & RUN2 & AG2).
       eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
       apply (pd_tail_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) r2 (0x252a0 + dVL_25134) (0x10749 + dVLS_10749) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW0 PM0 ltac:(intros; reflexivity) CE0
                ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR1 |- *; rest_solve)). cbn. left. reflexivity. }
  destruct (pd_B al_rom r1 M0 dp b0 b1 b2 b3 ltac:(lia) ltac:(lia) Hal4 Rb0 Rb1 Rb2 Rb3 E0 E1 E2 E3 P10') as (r2 & RUN2 & Q12 & Q13 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
  assert (RR2 : forall x, In x pd_rest -> getr r2 x = getr regs x) by (unfold pd_rest; rest_solve).
  (* [comment removed for export] *)
  destruct (payload_field M0 dp pl 4 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as [R4 B4]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in R4.
  set (wr := bytes_le_to_Z (firstn 4 (skipn 4 pl))) in B4.
  destruct (Z_le_gt_dec 1 wr) as [W1|W1]; [destruct (Z_le_gt_dec wr 1000000) as [W2|W2]|].
  2,3: destruct (pd_Cbad al_rom r2 M0 dp wr _ ltac:(lia) ltac:(lia) R4 eq_refl B4 ltac:(lia) ltac:(csr; reflexivity)) as (r3 & RUN3 & AG3);
       eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN3 |];
       replace (rl dVL_25134 0x25278) with (rl dVL_25134 0x25278) by (apply bv_eq; reflexivity);
       apply (pd_tail_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) r3 (0x25278 + dVL_25134) (0x1097f + dVLS_1097f) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW0 PM0 ltac:(intros; reflexivity) CE0
                ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR2 |- *; rest_solve)); cbn; right; left; reflexivity.
  destruct (pd_C al_rom r2 M0 dp wr _ ltac:(lia) ltac:(lia) R4 eq_refl ltac:(lia) ltac:(csr; reflexivity)) as (r3 & RUN3 & Q9 & Q13' & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN3 |].
  assert (RR3 : forall x, In x pd_rest -> getr r3 x = getr regs x) by (unfold pd_rest; rest_solve).
  (* [comment removed for export] *)
  destruct (payload_field M0 dp pl 8 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as [R8 B8]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in R8.
  set (hr := bytes_le_to_Z (firstn 4 (skipn 8 pl))) in B8.
  destruct (Z_le_gt_dec 1 hr) as [X1|X1]; [destruct (Z_le_gt_dec hr 1000000) as [X2|X2]|].
  2,3: destruct (pd_Dbad al_rom r3 M0 dp hr _ ltac:(lia) ltac:(lia) R8 eq_refl B8 ltac:(lia) ltac:(csr; reflexivity) Q13') as (r4 & RUN4 & AG4);
       eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN4 |];
       replace (rl dVL_25134 0x25300) with (rl dVL_25134 0x25300) by (apply bv_eq; reflexivity);
       apply (pd_tail_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) r4 (0x25300 + dVL_25134) (0x1034c + dVLS_1034c) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW0 PM0 ltac:(intros; reflexivity) CE0
                ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR3 |- *; rest_solve)); cbn; repeat (first [left; reflexivity | right]).
  destruct (pd_D al_rom r3 M0 dp hr _ ltac:(lia) ltac:(lia) R8 eq_refl ltac:(lia) ltac:(csr; reflexivity) Q13') as (r4 & RUN4 & Q18 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN4 |].
  assert (RR4 : forall x, In x pd_rest -> getr r4 x = getr regs x) by (unfold pd_rest; rest_solve).
  assert (Q9' : getr r4 9 = Z_to_bv 64 wr) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (Z_le_gt_dec (wr * hr) 400000000) as [AR|AR].
  2: { destruct (pd_Ebad al_rom r4 M0 wr hr ltac:(lia) ltac:(lia) ltac:(lia) Q9' Q18) as (r5 & RUN5 & AG5).
       eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN5 |].
       apply (pd_tail_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) r5 (0x25338 + dVL_25134) (0x10322 + dVLS_10322) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW0 PM0 ltac:(intros; reflexivity) CE0
                ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR4 |- *; rest_solve)). cbn. repeat (first [left; reflexivity | right]). }
  destruct (pd_E al_rom r4 M0 wr hr ltac:(lia) ltac:(lia) AR Q9' Q18) as (r5 & RUN5 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN5 |].
  assert (RR5 : forall x, In x pd_rest -> getr r5 x = getr regs x) by (unfold pd_rest; rest_solve).
  (* [comment removed for export] *)
  destruct (payload_field M0 dp pl 20 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as [R20 B20]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in R20.
  set (ncr := bytes_le_to_Z (firstn 4 (skipn 20 pl))) in B20.
  destruct (payload_field M0 dp pl 12 BAT ltac:(lia) ltac:(lia) ltac:(lia)) as [R12 B12]. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in R12.
  set (dr := bytes_le_to_Z (firstn 4 (skipn 12 pl))) in B12.
  set (q := (nb / 4)%Z).
  assert (Hq : (4 * q <= nb)%Z) by (subst q; apply Z.mul_div_le; lia).
  assert (NCD : {(ncr <= 256 /\ ncr + 7 < q)%Z} + {~ (ncr <= 256 /\ ncr + 7 < q)%Z}).
  { destruct (Z_le_gt_dec ncr 256); [|right; lia]. destruct (Z_lt_ge_dec (ncr + 7) q); [left; lia | right; lia]. }
  destruct NCD as [[NC1 NC2] | NCB].
  2: { destruct (pd_Fbad al_rom r5 M0 dp nb ncr q _ ltac:(lia) ltac:(lia) ltac:(lia) eq_refl R20 eq_refl B20 NCB ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)) as (r6 & RUN6 & AG6).
       eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN6 |].
       apply (pd_tail_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) r6 (0x25470 + dVL_25134) (0x1079f + dVLS_1079f) CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW0 PM0 ltac:(intros; reflexivity) CE0
                ltac:(csr; reflexivity) ltac:(unfold pd_rest in RR5 |- *; rest_solve)). cbn. repeat (first [left; reflexivity | right]). }
  destruct (pd_F al_rom r5 M0 dp nb ncr q dr wr hr _ _ ltac:(lia) ltac:(lia) ltac:(lia) eq_refl R20 eq_refl ltac:(lia) NC2 R12 eq_refl B12 ltac:(lia) ltac:(lia)
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r6 & RUN6 & V22 & V20 & V23 & V19 & V10 & V11 & V12 & V1 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN6 |].
  assert (RR6 : forall x, In x pd_rest -> getr r6 x = getr regs x) by (unfold pd_rest; rest_solve).
  pose proof (zx_range (sw32 dr)) as Hd64.
  apply (pixCreateHeader_W C A M0 _ r6 (s - 96) wr hr (zx (sw32 dr)) (rl dVL_25134 0x25394) S CK HW0 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(rl_ret_ok_VL) ltac:(csr; reflexivity) V10 V11 V12 ltac:(lia) ltac:(lia) AR Hd64).
  intros A1 M1 vm1 r7 HW1 CS1 PM1 RES1 HRT1. rewrite with_vmmaps_twice in HW1 |- *.
  pose proof PM1 as [F1 L1].
  apply (pd_hdr_W C A m md regs s ret S kR bR A1 M1 vm1 r7 dp pl ncr wr hr dr (bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * ncr + 24)) pl)))
           CK HK ltac:(room_tac) Hrk Hrb Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 H4 PLD ltac:(fold nb; lia) ltac:(lia) ltac:(fold nb; lia) ltac:(lia) ltac:(lia) AR ltac:(lia) eq_refl HW1).
  - eapply POSTM_trans; [exact PM0|]. apply (POSTM_sub C (c_A0 C) A); [exact (W_sub0 _ _ _ _ HW0)|]. eapply POSTM_mono; [|exact PM1]. lia.
  - exact (cells_frm C (s - 96) M0 M1 s ret _ CK F1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) CE0).
  - csr; reflexivity.
  - unfold pd_rest in RR6 |- *; rest_solve.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - csr; reflexivity.
  - exact Hal4.
  - exact RES1.
Qed.

End Deser.
