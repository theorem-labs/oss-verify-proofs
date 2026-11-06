(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptCmap V2LeptPixDestroy V2LeptPixHdr V2LeptPadBitsW V2LeptPixCreate V2LeptPixHdrT2 V2LeptPixCreateT2 V2LeptCmapDeser V2LeptCmapValid V2MemcpyBase V2Memcpy V2LeptDeserA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomBL LeptRoomBD.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require LiaFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocVL.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2RelocMusl V2LeptEnv V2LeptG.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac roomT_margins :=
  repeat match goal with
         | H : context [alloc_margin ?n] |- _ =>
             lazymatch goal with
             | _ : (alloc_margin n <= n + 2 ^ 22)%Z |- _ => fail
             | _ => pose proof (alloc_margin_le n)
             end
         end.
(* [comment removed for export] *)
Ltac roomT_zeta := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end.
Ltac roomT_subst := repeat match goal with E : ?x = _ |- _ => is_var x; subst x end.
Ltac roomT_prep := cbn [p_w p_h p_d p_cmap p_data] in *; unfold hdr_ok in *; roomT_zeta; roomT_subst;
                   unfold RB_deserT, RB_rasT, RB_pixT, RB_hdrT in *; roomT_margins.
Ltac roomT_tac := roomT_prep; room_tac.

Section Deser.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma str_pixDeserialize : str16 0x11227 24.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e2 : str16 0x115c4 17.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e3 : str16 0x11f8e 13.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e4 : str16 0x105b3 14.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e5 : str16 0x10413 14.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e6 : str16 0x117ba 15.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e7 : str16 0x10bb4 21.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e9 : str16 0x119a6 12.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e10 : str16 0x124ff 13.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e12 : str16 0x1085d 24.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e1 : str16 0x115a1 34.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.
Lemma str_e8 : str16 0x10e9c 83.
Proof.
  unfold str16. split; [vm_compute; reflexivity|].
  split; [lia|]. split; [lia|]. apply Z.leb_le. vm_compute. reflexivity.
Qed.

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
Definition DKT (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s : Z) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C (c_A0 C) s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix v cv, getr regs' 10 = Z_to_bv 64 pix /\ pixobj C A A' m' pix v cv /\ pixfacts v cv)) ->
     aroom A' vm' (kR - RK_deser) (bR - RB_deserT) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

#[local] Definition pd_rest : list (bv 5) := [3; 4; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma pd_eptr_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (pc msg : Z),
  Cok C -> DKT C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_deser) (bR - RB_deserT) -> (RK_deser <= kR)%Z -> (RB_deserT <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M -> (forall q, live A1 q = live A q) ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  In (pc, msg) ej_leaves ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 pc) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A m md regs s ret S kR bR A1 M vm1 r pc msg ok_C kont room1 k_ge b_ge sp_al sp_lo sp_hi ret_good sp_regs
    w_M post_M live_same frame_M sp_r rest_r leaf.
  unfold pd_rest in rest_r. unfold DKT in kont.
  pose proof (ck_img C ok_C) as img_lo. cbn [ll_img LLU16 snd] in img_lo.
  pose proof (ck_top C ok_C) as top_lo. pose proof (ck_sp0 C ok_C) as top_sp0. pose proof (ck_sp0hi C ok_C) as sp0_hi.
  pose proof LSTK_val as lstk. assert (lsf : LSF = 3376%Z) by reflexivity.
  destruct (ej_str pc msg leaf) as [kmsg str_msg].
  destruct (pd_EJ al_rom pc msg r M leaf (W_sev_got C A1 M _ w_M) (W_sev C A1 M _ w_M))
    as (g1 & run1 & a0_g1 & a1_g1 & a2_g1 & ra_g1 & agr1).
  pose proof (w_pure _ _ _ _ w_M) as pure1.
  apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run1).
  assert (sp_g1 : getr g1 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  assert (al96 : ((s - 96) mod 16 = 0)%Z).
  { replace (s - 96)%Z with (s + (-6) * 16)%Z by lia. rewrite Z_mod_plus_full. exact sp_al. }
  apply (returnErrorPtr_W C A1 M (with_vmmaps vm1 md) g1 (s - 96) msg 0x11227 kmsg 24 (0x37bd0 : word) (Z_to_bv 64 0) S
           ok_C w_M sp_g1 al96 ltac:(lia) ltac:(lia) ltac:(rewrite ra_g1; apply bv_eq; reflexivity)
           ltac:(apply ret_ok_even; reflexivity) a0_g1 a1_g1 a2_g1 str_msg str_pixDeserialize).
  intros M2 g2 w_M2 out_M2 grow_M2 kept_g2 a0_g2.
  destruct (pd_J7c al_rom g2 M2) as (g3 & run3 & agr3).
  apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run3).
  assert (frame_M2 : cellsZ M2 (frame9 s ret (svr regs))).
  { apply (cells_out M M2 (s - 96 - (16 + LSF)) (s - 96) s ret (svr regs) out_M2); first [exact frame_M | lia]. }
  assert (sp_g3 : getr g3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  destruct (pd_RET al_rom g3 M2 s ret (svr regs) ltac:(lia) ltac:(lia) ret_good (pd_cells_of M2 s ret (svr regs) frame_M2) sp_g3)
    as (g4 & run4 & sp_g4 & ra_g4 & s0_g4 & s1_g4 & s2_g4 & s3_g4 & s4_g4 & s5_g4 & s6_g4 & s7_g4 & agr4).
  apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run4).
  apply (kont A1 M2 vm1 g4 w_M2).
  - apply cs_kept_intro; csr; reflexivity.
  - apply (POSTM_trans C (c_A0 C) s m M M2 post_M).
    apply (POSTM_sub C (c_A0 C) A1 s M M2 (W_sub0 _ _ _ _ w_M)).
    apply (POSTM_range C A1 M (with_vmmaps vm1 md) M2 (s - 96 - (16 + LSF)) (s - 96) s ok_C w_M out_M2); lia.
  - left. split; [csr; reflexivity | exact live_same].
  - exact room1.
Qed.

(* [comment removed for export] *)
Lemma pd_tail_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (pc msg : Z),
  Cok C -> DKT C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_deser) (bR - RB_deserT) -> (RK_deser <= kR)%Z -> (RB_deserT <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M -> (forall q, live A1 q = live A q) ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  In (pc, msg) et_leaves ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 pc) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A m md regs s ret S kR bR A1 M vm1 r pc msg ok_C kont room1 k_ge b_ge sp_al sp_lo sp_hi ret_good sp_regs
    w_M post_M live_same frame_M sp_r rest_r leaf.
  unfold pd_rest in rest_r. unfold DKT in kont.
  pose proof (w_pure _ _ _ _ w_M) as pure1.
  pose proof (ck_img C ok_C) as img_lo. cbn [ll_img LLU16 snd] in img_lo.
  pose proof (ck_top C ok_C) as top_lo. pose proof (ck_sp0 C ok_C) as top_sp0. pose proof (ck_sp0hi C ok_C) as sp0_hi.
  pose proof LSTK_val as lstk. assert (lsf : LSF = 3376%Z) by reflexivity.
  assert (s_rng : (96 <= s < 2 ^ 64)%Z) by lia.
  destruct (et_str pc msg leaf) as [kmsg str_msg].
  destruct (pd_ET al_rom pc msg r M leaf (W_sev_got C A1 M _ w_M) (W_sev C A1 M _ w_M)) as (g1 & run1 & a0_g1 & a1_g1 & agr1).
  apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run1).
  assert (sp_g1 : getr g1 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
  destruct (pd_X50 al_rom g1 M s ret (svr regs) (proj1 s_rng) (proj2 s_rng) (pd_cells_of M s ret (svr regs) frame_M) sp_g1)
    as (g2 & run2 & sp_g2 & ra_g2 & a2_g2 & s0_g2 & s1_g2 & s2_g2 & s3_g2 & s4_g2 & s5_g2 & s6_g2 & s7_g2 & agr2).
  apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run2).
  assert (a0_g2 : getr g2 10 = Z_to_bv 64 msg) by (csr; reflexivity).
  assert (a1_g2 : getr g2 11 = Z_to_bv 64 0x11227) by (csr; reflexivity).
  apply (returnErrorPtr_W C A1 M (with_vmmaps vm1 md) g2 s msg 0x11227 kmsg 24 ret (Z_to_bv 64 0) S
           ok_C w_M sp_g2 sp_al ltac:(lia) sp_hi ra_g2 ret_good a0_g2 a1_g2 a2_g2 str_msg str_pixDeserialize).
  intros M2 g3 w_M2 out_M2 grow_M2 kept_g3 a0_g3.
  apply (kont A1 M2 vm1 g3 w_M2).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact post_M|].
    eapply POSTM_sub; [exact (W_sub0 _ _ _ _ w_M)|].
    apply (POSTM_range C A1 M (with_vmmaps vm1 md) M2 (s - (16 + LSF)) s s ok_C w_M out_M2); lia.
  - left. split; [exact a0_g3 | exact live_same].
  - exact room1.
Qed.

(* [comment removed for export] *)
Lemma pd_lerr_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (fmt retpc : Z) kf,
  Cok C -> DKT C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_deser) (bR - RB_deserT) -> (RK_deser <= kR)%Z -> (RB_deserT <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M -> (forall q, live A1 q = live A q) ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 10 = Z_to_bv 64 fmt -> getr r 11 = Z_to_bv 64 0x11227 -> getr r 1 = Z_to_bv 64 retpc -> (retpc = 0x37788 \/ retpc = 0x37adc)%Z ->
  In fmt (SSP.ls_fmts1 L16) -> str16 fmt kf ->
  realizes SEGS (mkCfg (mkst r (0x17e28 : word) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A m md regs s ret S kR bR A1 M vm1 r fmt retpc kf ok_C kont room1 k_ge b_ge sp_al sp_lo sp_hi ret_good sp_regs
    w_M post_M live_same frame_M sp_r rest_r a0_r a1_r ra_r ret_site fmt_in str_fmt.
  unfold pd_rest in rest_r. unfold DKT in kont.
  pose proof (w_pure _ _ _ _ w_M) as pure1.
  pose proof (ck_img C ok_C) as img_lo. cbn [ll_img LLU16 snd] in img_lo.
  pose proof (ck_top C ok_C) as top_lo. pose proof (ck_sp0 C ok_C) as top_sp0. pose proof (ck_sp0hi C ok_C) as sp0_hi.
  pose proof LSTK_val as lstk. assert (lsf : LSF = 3376%Z) by reflexivity.
  assert (al96 : ((s - 96) mod 16 = 0)%Z).
  { replace (s - 96)%Z with (s + (-6) * 16)%Z by lia. rewrite Z_mod_plus_full. exact sp_al. }
  assert (epilogue : forall (M2 : word -> option byte) (g2 : bvmap 5 word), W C A1 M2 (with_vmmaps vm1 md) ->
            (forall a : word, ~ (s - 96 - LSF <= u a < s - 96)%Z -> M2 a = M a) -> cs_kept r g2 ->
            realizes RSEGS (mkCfg (mkst g2 (0x37bd4 : word) M2 al_rom) (with_vmmaps vm1 md)) S).
  { intros M2 g2 w_M2 out_M2 kept_g2.
    destruct (pd_R0 al_rom g2 M2) as (g3 & run3 & a0_g3 & agr3).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run3).
    assert (frame_M2 : cellsZ M2 (frame9 s ret (svr regs))).
    { apply (cells_out M M2 (s - 96 - LSF) (s - 96) s ret (svr regs) out_M2); first [exact frame_M | lia]. }
    assert (sp_g3 : getr g3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    destruct (pd_RET al_rom g3 M2 s ret (svr regs) ltac:(lia) ltac:(lia) ret_good (pd_cells_of M2 s ret (svr regs) frame_M2) sp_g3)
      as (g4 & run4 & sp_g4 & ra_g4 & s0_g4 & s1_g4 & s2_g4 & s3_g4 & s4_g4 & s5_g4 & s6_g4 & s7_g4 & agr4).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run4).
    apply (kont A1 M2 vm1 g4 w_M2).
    - apply cs_kept_intro; csr; reflexivity.
    - apply (POSTM_trans C (c_A0 C) s m M M2 post_M).
      apply (POSTM_sub C (c_A0 C) A1 s M M2 (W_sub0 _ _ _ _ w_M)).
      apply (POSTM_range C A1 M (with_vmmaps vm1 md) M2 (s - 96 - LSF) (s - 96) s ok_C w_M out_M2); lia.
    - left. split; [csr; reflexivity | exact live_same].
    - exact room1. }
  destruct ret_site as [site | site]; subst retpc.
  - apply (lept_stderr1_W C A1 M (with_vmmaps vm1 md) r (s - 96) fmt 0x11227 kf 24 (Z_to_bv 64 0x37788) S
             ok_C w_M sp_r al96 ltac:(lia) ltac:(lia) ra_r ltac:(apply ret_ok_even; reflexivity) a0_r a1_r fmt_in str_fmt
             str_pixDeserialize).
    intros M2 g2 w_M2 out_M2 _ kept_g2.
    replace (Z_to_bv 64 0x37788) with (0x37788 : word) by (apply bv_eq; reflexivity).
    destruct (pd_J34 al_rom g2 M2) as (g3 & run3 & agr3).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run3).
    apply (epilogue M2 g3 w_M2 out_M2).
    intros x x_cs. rewrite (agr3 x (fun no => no)). exact (cs_kept_get r g2 x kept_g2 x_cs).
  - apply (lept_stderr1_W C A1 M (with_vmmaps vm1 md) r (s - 96) fmt 0x11227 kf 24 (Z_to_bv 64 0x37adc) S
             ok_C w_M sp_r al96 ltac:(lia) ltac:(lia) ra_r ltac:(apply ret_ok_even; reflexivity) a0_r a1_r fmt_in str_fmt
             str_pixDeserialize).
    intros M2 g2 w_M2 out_M2 _ kept_g2.
    replace (Z_to_bv 64 0x37adc) with (0x37adc : word) by (apply bv_eq; reflexivity).
    destruct (pd_J88 al_rom g2 M2) as (g3 & run3 & agr3).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run3).
    apply (epilogue M2 g3 w_M2 out_M2).
    intros x x_cs. rewrite (agr3 x (fun no => no)). exact (cs_kept_get r g2 x kept_g2 x_cs).
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
  Cok C -> DKT C A m md regs s ret S kR bR ->
  aroom A5 vm5 (kR - RK_deser) (bR - RB_deserT) -> (RK_deser <= kR)%Z -> (RB_deserT <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  payload C dp pl ->
  (0 <= nc <= 256)%Z -> (4 * nc + 28 + 4 * (wpl_of w d * h) = Z.of_nat (length pl))%Z -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  W C A5 M (with_vmmaps vm5 md) -> POSTM C (c_A0 C) s m M ->
  pixobj C A A5 M pixd (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) cv ->
  (nc = 0 <-> cm = 0)%Z -> (cm <> 0%Z -> cmap_ok cv) ->
  cellsZ M (frame9 s ret (svr regs)) -> rdn SEGS M (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 10 = Z_to_bv 64 data -> getr r 11 = Z_to_bv 64 (dp + 4 * nc + 28) -> getr r 12 = Z_to_bv 64 (4 * (wpl_of w d * h)) ->
  getr r 1 = Z_to_bv 64 0x37b78 -> getr r 22 = Z_to_bv 64 nc -> getr r 9 = Z_to_bv 64 cm -> getr regs 4 = Z_to_bv 64 0x56270 ->
  realizes SEGS (mkCfg (mkst r (0x4347c : word) M al_rom) (with_vmmaps vm5 md)) S.
Proof.
  intros C A m md regs s ret S kR bR A5 M vm5 r dp pl nc w h d pixd data cm cv ok_C kont room5 k_ge b_ge sp_al sp_lo sp_hi
    ret_good sp_regs pay nc_rng len_pl hdr w_pos h_pos w_M post_M pobj nc_iff cm_ok frame_M slot_M sp_r rest_r
    a0_r a1_r a2_r ra_r s6_r s1_r gp_regs.
  unfold pd_rest in rest_r. unfold DKT in kont.
  set (md5 := with_vmmaps vm5 md) in *.
  set (sz := (4 * (wpl_of w d * h))%Z) in *.
  set (v := PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) in *.
  pose proof (w_pure _ _ _ _ w_M) as pure5.
  pose proof (ck_img C ok_C) as img_lo. cbn [ll_img LLU16 snd] in img_lo.
  pose proof (ck_top C ok_C) as top_lo. pose proof (ck_sp0 C ok_C) as top_sp0. pose proof (ck_sp0hi C ok_C) as sp0_hi.
  pose proof LSTK_val as lstk. assert (lsf : LSF = 3376%Z) by reflexivity.
  pose proof (alloc_top_lt (c_vm C)) as top64. unfold two_pow_64 in top64.
  assert (s_rng : (96 <= s < 2 ^ 64)%Z) by lia.
  assert (s16 : s = (16 * (s / 16))%Z) by (pose proof (Z.div_mod s 16 ltac:(lia)); lia).
  destruct hdr as (dval_d & w_hi & h_hi & sz_hi).
  pose proof pobj as (px_M & rc_v & text_v & sz_pos & lv_pix & lvA_pix & lv0_pix & lv_data & lvA_data & lv0_data & data_pix & cmap_v & others_v).
  cbn [p_wpl p_h p_data p_cmap p_rc p_text v] in rc_v, text_v, sz_pos, lv_data, lvA_data, lv0_data, data_pix, cmap_v, others_v.
  pose proof px_M as (pixd_lo & pixd_hi & wf_v & _).
  pose proof (wf_data v wf_v) as data_rng. cbn [p_data v] in data_rng.
  destruct pay as (lv0_dp & bytes0 & dp_lo & dp_hi).
  pose proof (payload_at C A5 M md5 dp pl w_M (conj lv0_dp (conj bytes0 (conj dp_lo dp_hi)))) as bytes_M.
  pose proof (W_sub0 _ _ _ _ w_M) as sub5.
  pose proof (sub5 _ _ lv0_dp) as lv_dp.
  destruct (blk_range C A5 M md5 (Z_to_bv 64 data) sz ok_C w_M lv_data sz_pos) as [data_lo data_top].
  destruct (blk_range C A5 M md5 (Z_to_bv 64 pixd) 64 ok_C w_M lv_pix ltac:(lia)) as [pixd_lo' pixd_top].
  rewrite u_Z2bv in data_lo, data_top, pixd_lo', pixd_top by lia.
  assert (data_apart : (data + sz <= dp \/ dp + Z.of_nat (length pl) <= data)%Z).
  { assert (data_ne_dp : Z_to_bv 64 data <> Z_to_bv 64 dp) by (intros same; rewrite same in lv0_data; congruence).
    destruct (live_apart C A5 M md5 _ _ sz (Z.of_nat (length pl)) ok_C w_M lv_data lv_dp data_ne_dp ltac:(lia) ltac:(lia))
      as [o | o]; rewrite !u_Z2bv in o by lia; lia. }
  assert (pix_apart : (pixd + 64 <= data \/ data + sz <= pixd)%Z).
  { destruct (live_apart C A5 M md5 (Z_to_bv 64 pixd) (Z_to_bv 64 data) 64 sz ok_C w_M lv_pix lv_data
                (zbv_ne pixd data ltac:(lia) ltac:(lia) (fun e => data_pix (eq_sym e))) ltac:(lia) ltac:(lia)) as [o | o];
      rewrite !u_Z2bv in o by lia; lia. }
  set (bs := firstn (Z.to_nat sz) (skipn (Z.to_nat (4 * nc + 28)) pl)).
  assert (len_bs : length bs = Z.to_nat sz) by (subst bs; rewrite length_firstn, length_skipn; lia).
  assert (mc : mcH M (Z_to_bv 64 data) (Z_to_bv 64 (dp + 4 * nc + 28)) sz bs).
  { constructor.
    - lia.
    - exact len_bs.
    - rewrite len_bs. subst bs.
      replace (dp + 4 * nc + 28)%Z with (dp + Z.of_nat (Z.to_nat (4 * nc + 28)))%Z by lia.
      apply bytes_at_field; [lia | lia | lia | exact bytes_M].
    - apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
      intros x x_in.
      destruct (blk_byte C A5 M md5 (Z_to_bv 64 data) sz x ok_C w_M lv_data ltac:(rewrite u_Z2bv by lia; lia)) as (_ & def_x & _).
      unfold wview. destruct (M x); [discriminate | contradiction].
    - rewrite !u_Z2bv by lia. lia.
    - rewrite u_Z2bv by lia. lia.
    - rewrite u_Z2bv by lia. lia. }
  destruct (ref_memcpy M (Z_to_bv 64 data) (Z_to_bv 64 (dp + 4 * nc + 28)) sz bs al_rom mc r (Z_to_bv 64 0x37b78)
              ltac:(apply ret_ok_even; reflexivity) ra_r a0_r a1_r a2_r) as (g1 & run1 & kept1).
  apply (rz_msteps _ _ _ _ _ (mp_halted _ pure5) (mp_lazy _ pure5) run1).
  replace (Z_to_bv 64 0x37b78) with (0x37b78 : word) by (apply bv_eq; reflexivity).
  assert (sp_g1 : getr g1 2 = Z_to_bv 64 (s - 96)) by (rewrite (keeps_getr r g1 2 kept1 ltac:(in_kept)); exact sp_r).
  assert (s6_g1 : getr g1 22 = Z_to_bv 64 nc) by (rewrite (keeps_getr r g1 22 kept1 ltac:(in_kept)); exact s6_r).
  assert (s1_g1 : getr g1 9 = Z_to_bv 64 cm) by (rewrite (keeps_getr r g1 9 kept1 ltac:(in_kept)); exact s1_r).
  assert (rest_g1 : forall x : reg, In x [3; 4; 24; 25; 26; 27]%bv -> getr g1 x = getr regs x).
  { intros x x_in. rewrite <- (rest_r x x_in).
    apply (keeps_getr r g1 x kept1). destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; in_kept. }
  set (M1 := wbytes M (Z_to_bv 64 data) bs).
  assert (out_M1 : forall x : word, ~ (data <= u x < data + sz)%Z -> M1 x = M x).
  { intros x x_out. apply wbytes_outside; rewrite ?u_Z2bv, ?len_bs by lia; lia. }
  assert (wp1 : W C A5 M1 md5 /\ POSTM C (c_A0 C) s m M1).
  { apply (WP_blk C (c_A0 C) A5 m M md5 (Z_to_bv 64 data) (Z_to_bv 64 data) sz bs s ok_C (conj w_M post_M) lv_data lv0_data lv0_data sub5);
      rewrite ?u_Z2bv, ?len_bs by lia; lia. }
  destruct wp1 as [w_M1 post_M1].
  assert (slot_M1 : rdn RSEGS M1 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
  { apply (rdn_after M M1 data (data + sz) (s - 96) 8 _ out_M1); [lia | lia | lia | exact slot_M]. }
  assert (frame_M1 : cellsZ M1 (frame9 s ret (svr regs))).
  { apply (cells_out M M1 data (data + sz) s ret (svr regs) out_M1); first [exact frame_M | lia]. }
  assert (pobj1 : pixobj C A A5 M1 pixd v cv).
  { apply (pixobj_keep C A A5 M M1 pixd v cv pobj).
    - intros x x_in. apply out_M1. lia.
    - cbn [p_cmap v]. intros cm_nz x x_in. apply out_M1.
      destruct cmap_v as [cm0 | (cm_lo & cmap_M & lv_cm & _ & _ & _ & _ & _ & _ & _ & _ & _ & data_cm & _)]; [contradiction|].
      pose proof cmap_M as (_ & cm_hi & _).
      destruct (live_apart C A5 M md5 (Z_to_bv 64 cm) (Z_to_bv 64 data) 24 sz ok_C w_M lv_cm lv_data
                  (zbv_ne cm data ltac:(lia) ltac:(lia) (fun e => data_cm (eq_sym e))) ltac:(lia) ltac:(lia)) as [o | o];
        rewrite !u_Z2bv in o by lia; lia. }
  assert (facts_v : pixfacts v cv).
  { unfold pixfacts. cbn [p_w p_h p_d p_cmap p_data v]. split; [reflexivity|].
    split; [exact (conj dval_d (conj w_hi (conj h_hi sz_hi)))|]. split; [exact w_pos|]. split; [exact h_pos | exact cm_ok]. }
  destruct (Z.eq_dec nc 0) as [nc0 | nc_nz].
  - destruct (pd_L0 al_rom g1 M1 s pixd (proj1 s_rng) (proj2 s_rng) ltac:(lia) slot_M1 sp_g1 ltac:(rewrite s6_g1, nc0; reflexivity))
      as (g2 & run2 & a0_g2 & agr2).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure5) (mp_lazy _ pure5) run2).
    assert (sp_g2 : getr g2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    destruct (pd_RET al_rom g2 M1 s ret (svr regs) (proj1 s_rng) (proj2 s_rng) ret_good (pd_cells_of M1 s ret (svr regs) frame_M1) sp_g2)
      as (g3 & run3 & sp_g3 & ra_g3 & s0_g3 & s1_g3 & s2_g3 & s3_g3 & s4_g3 & s5_g3 & s6_g3 & s7_g3 & agr3).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure5) (mp_lazy _ pure5) run3).
    apply (kont A5 M1 vm5 g3 w_M1 ltac:(apply cs_kept_intro; csr; reflexivity) post_M1); [|exact room5].
    right. exists pixd, v, cv. split; [csr; reflexivity|]. split; [exact pobj1 | exact facts_v].
  - assert (cm_nz : cm <> 0%Z) by (intros e; apply nc_nz; exact (proj2 nc_iff e)).
    destruct cmap_v as [cm0 | (cm_lo & cmap_M & lv_cm & lv_arr & arr_pos & lvA_cm & lvA_arr & lv0_cm & lv0_arr & cm_arr & cm_pix & arr_pix & data_cm & data_arr)];
      [contradiction|].
    pose proof (cm_ok cm_nz) as cmok.
    pose proof cmap_M as (_ & cm_hi & _).
    destruct (blk_range C A5 M md5 (Z_to_bv 64 cm) 24 ok_C w_M lv_cm ltac:(lia)) as [_ cm_top].
    rewrite u_Z2bv in cm_top by lia.
    pose proof pobj1 as (px_M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & cmap1 & _).
    cbn [p_cmap v] in cmap1.
    destruct cmap1 as [cm0 | (_ & cmap_M1 & _)]; [contradiction|].
    destruct (pd_L1 al_rom g1 M1 s pixd nc cm (proj1 s_rng) (proj2 s_rng) ltac:(lia) ltac:(lia) slot_M1 sp_g1 s6_g1 s1_g1)
      as (g2 & run2 & a0_g2 & a1_g2 & a2_g2 & ra_g2 & agr2).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure5) (mp_lazy _ pure5) run2).
    assert (sp_g2 : getr g2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    assert (al96 : ((s - 96) mod 16 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 96)%Z with ((s / 16 - 6) * 16)%Z by ring; apply Z_mod_mult).
    assert (al76 : ((s - 76) mod 4 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 76)%Z with ((4 * (s / 16) - 19) * 4)%Z by ring; apply Z_mod_mult).
    apply (pixcmapIsValid_pix_W C A5 M1 md5 g2 (s - 96) cm pixd (s - 76) cv v (0x37b8c : word) S ok_C w_M1 sp_g2 al96
             ltac:(lia) ltac:(lia) ltac:(lia) al76 ltac:(rewrite ra_g2; apply bv_eq; reflexivity) ltac:(apply ret_ok_even; reflexivity)
             a0_g2 a1_g2 a2_g2 cmap_M1 cmok lv_cm px_M1 lv_pix dval_d ltac:(cbn [p_w v]; lia) ltac:(cbn [p_h v]; lia) eq_refl lv_data).
    intros M2 g3 w_M2 kept_g3 (valid & valid01 & pvp & a0_g3).
    unfold pv_post in pvp.
    set (M1v := wbytes M1 (Z_to_bv 64 (s - 76)) (word_to_le_bytes 4 (Z_to_bv 64 valid))) in pvp.
    assert (out_M1v : forall x : word, ~ (s - 76 <= u x < s - 72)%Z -> M1v x = M1 x).
    { intros x x_out. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (w_M1v : W C A5 M1v md5).
    { apply W_store_win; [exact ok_C | exact w_M1 | |]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (frame_M2 : cellsZ M2 (frame9 s ret (svr regs))).
    { apply (cells_frm C (s - 96) M1v M2 s ret (svr regs) ok_C (proj1 pvp)); try lia.
      apply (cells_out M1 M1v (s - 76) (s - 72) s ret (svr regs) out_M1v); first [exact frame_M1 | lia]. }
    assert (slot_M2 : rdn RSEGS M2 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
    { rewrite (FRM_rdn16 C (s - 96) M1v M2 (s - 96) 8 ok_C (proj1 pvp)) by lia.
      apply (rdn_after M1 M1v (s - 76) (s - 72) (s - 96) 8 _ out_M1v); [lia | lia | lia | exact slot_M1]. }
    assert (flag_M2 : rdn RSEGS M2 (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 valid)).
    { rewrite (FRM_rdn16 C (s - 96) M1v M2 (s - 76) 4 ok_C (proj1 pvp)) by lia.
      subst M1v. rewrite rdn_wbytes_hit4 by (rewrite u_Z2bv by lia; lia). rewrite w2b_Z by lia. reflexivity. }
    assert (sp_g3 : getr g3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    assert (post_M2 : POSTM C (c_A0 C) s m M2).
    { apply (POSTM_trans C (c_A0 C) s m M1 M2 post_M1).
      apply (POSTM_trans C (c_A0 C) s M1 M1v M2).
      - apply (POSTM_sub C (c_A0 C) A5 s M1 M1v sub5).
        apply POSTM_wbytes_win with (md := md5); [exact ok_C | exact w_M1 | | |]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia;
          cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
      - apply (POSTM_mono C (c_A0 C) (s - 96) s M1v M2); [lia|].
        exact (POSTM_sub C (c_A0 C) A5 (s - 96) M1v M2 sub5 pvp). }
    assert (heap_M2 : forall (p k : Z) (x : word), live A5 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z ->
                        (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> M2 x = M1 x).
    { intros p k x lv_p p_lo p_top x_in.
      assert (at_x : at_ (Z_to_bv 64 p) (u x - p) = x).
      { unfold at_. rewrite u_Z2bv by lia. replace (p + (u x - p))%Z with (u x) by ring. apply zbv_self. }
      rewrite <- at_x, (proj2 pvp (Z_to_bv 64 p) k (u x - p)%Z lv_p ltac:(lia)), at_x.
      apply out_M1v. lia. }
    destruct valid01 as [valid0 | valid1]; subst valid.
    + destruct (pd_M0 al_rom g3 M2 s (proj1 s_rng) (proj2 s_rng) flag_M2 sp_g3) as (g4 & run4 & a0_g4 & ra_g4 & agr4).
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure5) (mp_lazy _ pure5) run4).
      assert (sp_g4 : getr g4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      assert (gp_g4 : getr g4 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
      assert (al8 : ((s - 96) mod 8 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 96)%Z with ((2 * (s / 16) - 12) * 8)%Z by ring; apply Z_mod_mult).
      assert (px_M2 : PIXat M2 pixd v).
      { apply (PIXat_frame M1 M2 pixd v px_M1). intros x x_in. exact (heap_M2 pixd 64%Z x lv_pix pixd_lo pixd_top x_in). }
      assert (cmap_M2 : CMAPat M2 cm cv).
      { apply (CMAPat_frame M1 M2 cm cv cmap_M1). intros x x_in. exact (heap_M2 cm 24%Z x lv_cm ltac:(lia) cm_top x_in). }
      apply (pixDestroy_W C A5 M2 md5 g4 (s - 96) (s - 96) pixd cm (4 * c_nalloc cv) sz v cv (0x37ba4 : word) S ok_C w_M2 sp_g4 al96
               ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) ltac:(rewrite ra_g4; apply bv_eq; reflexivity)
               ltac:(apply ret_ok_even; reflexivity) gp_g4 al8 a0_g4 ltac:(rewrite <- w2l_Z8 by lia; exact slot_M2) px_M2 eq_refl eq_refl eq_refl
               lv_pix lv0_pix).
      * right. cbn [p_data v]. split; [exact lv_data|]. split; [exact lv0_data|]. split; [exact sz_pos|]. split; [exact data_pix|].
        intros _. split; [exact data_cm | exact data_arr].
      * right. split; [exact cmap_M2|]. split; [exact lv_cm|]. split; [exact lv_arr|]. split; [exact lv0_cm|]. split; [exact lv0_arr|].
        split; [exact cm_arr|]. split; [exact cm_pix|]. split; [exact arr_pix | exact arr_pos].
      * intros A6 M3 vm6 g5 w_M3 kept_g5 freed post_M3 slot_M3 rt6.
        unfold pixd_post in freed. cbn [p_data v] in freed.
        destruct freed as (gone_pix & gone_data & gone_cmap & same_else).
        unfold md5 in rt6, w_M3 |- *. rewrite with_vmmaps_vmmaps in rt6. rewrite with_vmmaps_twice in w_M3 |- *.
        pose proof (rt6 _ _ room5 ltac:(lia) ltac:(lia)) as room6. rewrite !Z.sub_0_r in room6.
        replace (0x37ba4 : word) with (Z_to_bv 64 0x37ba4) by (apply bv_eq; reflexivity).
        apply (pd_eptr_W C A m md regs s ret S kR bR A6 M3 vm6 g5 0x37ba4 0x1085d ok_C kont room6 k_ge b_ge sp_al sp_lo sp_hi
                 ret_good sp_regs w_M3).
        -- apply (POSTM_trans C (c_A0 C) s m M2 M3 post_M2). apply (POSTM_mono C (c_A0 C) (s - 96 + 8) s M2 M3); [lia | exact post_M3].
        -- intros q. destruct (decide (q = Z_to_bv 64 pixd)) as [-> | q_pix]; [rewrite gone_pix; exact (eq_sym lvA_pix)|].
           destruct (decide (q = Z_to_bv 64 data)) as [-> | q_data]; [rewrite (gone_data ltac:(lia)); exact (eq_sym lvA_data)|].
           destruct (decide (q = Z_to_bv 64 cm)) as [-> | q_cm]; [rewrite (proj1 (gone_cmap cm_nz)); exact (eq_sym lvA_cm)|].
           destruct (decide (q = Z_to_bv 64 (c_arr cv))) as [-> | q_arr]; [rewrite (proj2 (gone_cmap cm_nz)); exact (eq_sym lvA_arr)|].
           rewrite (same_else q q_pix (fun _ => q_data) (fun _ => conj q_cm q_arr)).
           exact (others_v q q_pix q_data (fun _ => conj q_cm q_arr)).
        -- apply (cells_frm C (s - 96 + 8) M2 M3 s ret (svr regs) ok_C (proj1 post_M3)); first [exact frame_M2 | lia].
        -- csr. reflexivity.
        -- intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity.
        -- unfold ej_leaves. cbn [In]. right. right. left. reflexivity.
    + destruct (pd_M1 al_rom g3 M2 s pixd (proj1 s_rng) (proj2 s_rng) ltac:(lia) flag_M2 slot_M2 sp_g3) as (g4 & run4 & a0_g4 & agr4).
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure5) (mp_lazy _ pure5) run4).
      assert (sp_g4 : getr g4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      destruct (pd_RET al_rom g4 M2 s ret (svr regs) (proj1 s_rng) (proj2 s_rng) ret_good (pd_cells_of M2 s ret (svr regs) frame_M2) sp_g4)
        as (g5 & run5 & sp_g5 & ra_g5 & s0_g5 & s1_g5 & s2_g5 & s3_g5 & s4_g5 & s5_g5 & s6_g5 & s7_g5 & agr5).
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure5) (mp_lazy _ pure5) run5).
      apply (kont A5 M2 vm5 g5 w_M2 ltac:(apply cs_kept_intro; csr; reflexivity) post_M2); [|exact room5].
      right. exists pixd, v, cv. split; [csr; reflexivity|]. split; [|exact facts_v].
      apply (pixobj_keep C A A5 M1 M2 pixd v cv pobj1).
      * intros x x_in. exact (heap_M2 pixd 64%Z x lv_pix pixd_lo pixd_top x_in).
      * intros _ x x_in. exact (heap_M2 cm 24%Z x lv_cm ltac:(lia) cm_top x_in).
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
  Cok C -> DKT C A m md regs s ret S kR bR ->
  aroom A3 vm3 (kR - (RK_hdr + RK_pix)) (bR - (RB_hdrT + (RB_pixT (4 * (wpl_of w d * h))))) -> (RK_deser <= kR)%Z -> (RB_deserT <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x56270 ->
  payload C dp pl ->
  (0 <= nc <= 256)%Z -> (4 * nc + 28 + 4 * (wpl_of w d * h) = Z.of_nat (length pl))%Z -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  W C A3 M (with_vmmaps vm3 md) -> POSTM C (c_A0 C) s m M ->
  pixobj C A A3 M pixd (pixv0 w h d 0 data) cmap0 ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 10 = Z_to_bv 64 pixd -> getr r 22 = Z_to_bv 64 nc -> getr r 23 = Z_to_bv 64 dp ->
  getr r 8 = Z_to_bv 64 (4 * (wpl_of w d * h)) -> (dp mod 4 = 0)%Z ->
  realizes SEGS (mkCfg (mkst r (0x379e8 : word) M al_rom) (with_vmmaps vm3 md)) S.
Proof.
  intros C A m md regs s ret S kR bR A3 M vm3 r dp pl nc w h d pixd data ok_C kont room3 k_ge b_ge sp_al sp_lo sp_hi
    ret_good sp_regs gp_regs pay nc_rng len_pl hdr w_pos h_pos w_M post_M pobj frame_M sp_r rest_r a0_r s6_r s7_r s0_r dp_al.
  unfold pd_rest in rest_r.
  set (sz := (4 * (wpl_of w d * h))%Z) in *.
  pose proof (w_pure _ _ _ _ w_M) as pure3.
  pose proof (ck_img C ok_C) as img_lo. cbn [ll_img LLU16 snd] in img_lo.
  pose proof (ck_top C ok_C) as top_lo. pose proof (ck_sp0 C ok_C) as top_sp0. pose proof (ck_sp0hi C ok_C) as sp0_hi.
  pose proof LSTK_val as lstk. assert (lsf : LSF = 3376%Z) by reflexivity.
  pose proof (alloc_top_lt (c_vm C)) as top64. unfold two_pow_64 in top64.
  assert (s_rng : (96 <= s < 2 ^ 64)%Z) by lia.
  assert (s16 : s = (16 * (s / 16))%Z) by (pose proof (Z.div_mod s 16 ltac:(lia)); lia).
  assert (al96 : ((s - 96) mod 16 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 96)%Z with ((s / 16 - 6) * 16)%Z by ring; apply Z_mod_mult).
  pose proof hdr as (dval_d & w_hi & h_hi & sz_hi).
  pose proof pobj as (px_M & _ & _ & sz_pos & lv_pix & lvA_pix & lv0_pix & lv_data & lvA_data & lv0_data & data_pix & _ & others_v).
  unfold pixv0 in sz_pos, lv_data, lvA_data, lv0_data, data_pix, others_v. cbn [p_wpl p_h p_data p_cmap] in sz_pos, lv_data, lvA_data, lv0_data, data_pix, others_v.
  pose proof px_M as (pixd_lo & pixd_hi & wf_v & _).
  pose proof (wf_data _ wf_v) as data_rng. unfold pixv0 in data_rng. cbn [p_data] in data_rng.
  pose proof pay as (lv0_dp & _ & dp_lo & dp_hi).
  pose proof (W_sub0 _ _ _ _ w_M) as sub3.
  destruct (blk_range C A3 M _ (Z_to_bv 64 pixd) 64 ok_C w_M lv_pix ltac:(lia)) as [pixd_lo' pixd_top].
  destruct (blk_range C A3 M _ (Z_to_bv 64 data) sz ok_C w_M lv_data sz_pos) as [data_lo data_top].
  rewrite u_Z2bv in pixd_lo', pixd_top, data_lo, data_top by lia.
  assert (pix8 : (pixd mod 8 = 0)%Z).
  { destruct (ai_live_hull A3 M _ (Z_to_bv 64 pixd) 64 (w_inv _ _ _ _ w_M) lv_pix) as (_ & pix16 & _).
    rewrite u_Z2bv in pix16 by lia.
    replace pixd with (16 * (pixd / 16))%Z by (pose proof (Z.div_mod pixd 16 ltac:(lia)); lia).
    replace (16 * (pixd / 16))%Z with ((2 * (pixd / 16)) * 8)%Z by ring. apply Z_mod_mult. }
  assert (data4 : (data mod 4 = 0)%Z).
  { destruct (ai_live_hull A3 M _ (Z_to_bv 64 data) sz (w_inv _ _ _ _ w_M) lv_data) as (_ & data16 & _).
    rewrite u_Z2bv in data16 by lia.
    replace data with (16 * (data / 16))%Z by (pose proof (Z.div_mod data 16 ltac:(lia)); lia).
    replace (16 * (data / 16))%Z with ((4 * (data / 16)) * 4)%Z by ring. apply Z_mod_mult. }
  pose proof (W_sok_win C A3 M _ (s - 96) 96 ok_C w_M ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as sok.
  set (M1 := wbytes M (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
  assert (wp1 : W C A3 M1 (with_vmmaps vm3 md) /\ POSTM C (c_A0 C) s m M1).
  { apply (WP_win C A3 (c_A0 C) m M _ (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd)) s ok_C (conj w_M post_M) sub3);
      rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  destruct wp1 as [w_M1 post_M1].
  assert (out_M1 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> M1 x = M x).
  { intros x x_out. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
  assert (slot_M1 : rdn RSEGS M1 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
  { apply rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (frame_M1 : cellsZ M1 (frame9 s ret (svr regs))).
  { apply (cells_out M M1 (s - 96) (s - 88) s ret (svr regs) out_M1); first [exact frame_M | lia]. }
  assert (pobj1 : pixobj C A A3 M1 pixd (pixv0 w h d 0 data) cmap0).
  { apply (pixobj_keep C A A3 M M1 pixd _ cmap0 pobj).
    - intros x x_in. apply out_M1. lia.
    - unfold pixv0. cbn [p_cmap]. intros no. contradiction. }
  pose proof pobj1 as (px_M1 & _).
  destruct (Z.eq_dec nc 0) as [nc0 | nc_nz].
  - destruct (pd_I1 al_rom r M s pixd (proj1 s_rng) (proj2 s_rng) sok ltac:(lia) sp_r a0_r ltac:(rewrite s6_r, nc0; reflexivity))
      as (g1 & run1 & s1_g1 & s2_g1 & a0_g1 & agr1).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure3) (mp_lazy _ pure3) run1).
    fold M1.
    destruct (pd_GD al_rom g1 M1 pixd dp nc sz (pixv0 w h d 0 data) px_M1 ltac:(lia) pix8 nc_rng ltac:(lia) ltac:(lia) dp_al data4
                a0_g1 ltac:(csr; reflexivity) ltac:(rewrite s2_g1, nc0; reflexivity) ltac:(csr; reflexivity))
      as (g2 & run2 & a0_g2 & a1_g2 & a2_g2 & ra_g2 & s2_g2 & agr2).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure3) (mp_lazy _ pure3) run2).
    apply (pd_copy_W C A m md regs s ret S kR bR A3 M1 vm3 g2 dp pl nc w h d pixd data 0 cmap0 ok_C kont
             ltac:(roomT_tac) k_ge b_ge sp_al sp_lo sp_hi ret_good sp_regs pay nc_rng len_pl hdr w_pos h_pos w_M1 post_M1 pobj1
             ltac:(split; intros; [reflexivity | exact nc0]) ltac:(intros no; contradiction) frame_M1 slot_M1
             ltac:(csr; reflexivity) ltac:(unfold pd_rest; intros x x_in; destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity)
             a0_g2 a1_g2 a2_g2 ra_g2 ltac:(csr; reflexivity) ltac:(csr; reflexivity) gp_regs).
  - assert (nc_pos : (1 <= nc <= 256)%Z) by lia.
    destruct (pd_I2 al_rom r M s pixd dp nc (proj1 s_rng) (proj2 s_rng) sok ltac:(lia) nc_pos ltac:(lia) ltac:(lia) sp_r a0_r s6_r s7_r)
      as (g1 & run1 & a0_g1 & a1_g1 & a2_g1 & ra_g1 & s2_g1 & agr1).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure3) (mp_lazy _ pure3) run1).
    fold M1.
    assert (sp_g1 : getr g1 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    assert (gp_g1 : getr g1 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
    assert (room3' : aroom A3 (m_vmmaps (with_vmmaps vm3 md)) (kR - (RK_hdr + RK_pix)) (bR - (RB_hdrT + RB_pixT sz))).
    { rewrite with_vmmaps_vmmaps. exact room3. }
    pose proof (RB_pixT_le26 sz ltac:(lia)) as pixT_le.
    apply (pixcmapDeserialize_W C A3 M1 _ g1 (s - 96) (dp + 24) nc (Z_to_bv 64 dp) (Z.of_nat (length pl)) (0x37a10 : word) S
             ok_C w_M1 sp_g1 al96 ltac:(lia) ltac:(lia) ltac:(rewrite ra_g1; apply bv_eq; reflexivity) ltac:(apply ret_ok_even; reflexivity)
             gp_g1 a0_g1 a1_g1 a2_g1 nc_pos lv0_dp ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; lia)
             _ _ room3' ltac:(unfold RK_cmap, RK_hdr, RK_pix, RK_deser in *; lia)
             ltac:(unfold RB_deserT in b_ge; lia)).
    intros A4 M2 vm4 g2 w_M2 kept_g2 post_M2 made room4.
    assert (heap_M2 : forall (p k : Z) (x : word), live A3 (Z_to_bv 64 p) = Some k -> (0 <= p)%Z ->
                        (p + k <= alloc_top (c_vm C))%Z -> (p <= u x < p + k)%Z -> M2 x = M1 x).
    { intros p k x lv_p p_lo p_top x_in.
      assert (at_x : at_ (Z_to_bv 64 p) (u x - p)%Z = x).
      { unfold at_. rewrite u_Z2bv by lia. replace (p + (u x - p))%Z with (u x) by ring. apply zbv_self. }
      rewrite <- at_x. exact (proj2 post_M2 (Z_to_bv 64 p) k (u x - p)%Z lv_p ltac:(lia)). }
    assert (px_M2 : PIXat M2 pixd (pixv0 w h d 0 data)).
    { apply (PIXat_frame M1 M2 pixd _ px_M1). intros x x_in. exact (heap_M2 pixd 64%Z x lv_pix pixd_lo pixd_top x_in). }
    assert (slot_M2 : rdn RSEGS M2 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
    { rewrite (FRM_rdn16 C (s - 96) M1 M2 (s - 96) 8 ok_C (proj1 post_M2)) by lia. exact slot_M1. }
    assert (frame_M2 : cellsZ M2 (frame9 s ret (svr regs))).
    { apply (cells_frm C (s - 96) M1 M2 s ret (svr regs) ok_C (proj1 post_M2)); first [exact frame_M1 | lia]. }
    assert (post_M2' : POSTM C (c_A0 C) s m M2).
    { apply (POSTM_trans C (c_A0 C) s m M1 M2 post_M1). apply (POSTM_mono C (c_A0 C) (s - 96) s M1 M2); [lia|].
      exact (POSTM_sub C (c_A0 C) A3 (s - 96) M1 M2 sub3 post_M2). }
    assert (sp_g2 : getr g2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    rewrite with_vmmaps_twice in w_M2 |- *.
    destruct made as [(a0_g2 & same4) | (cm & arr & a0_g2 & cnew)].
    + destruct (pd_J0 al_rom g2 M2 s (proj1 s_rng) (proj2 s_rng) sp_g2 a0_g2) as (g3 & run3 & a0_g3 & ra_g3 & agr3).
      pose proof (w_pure _ _ _ _ w_M2) as pure4.
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure4) (mp_lazy _ pure4) run3).
      assert (sp_g3 : getr g3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      assert (gp_g3 : getr g3 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
      assert (al8 : ((s - 96) mod 8 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 96)%Z with ((2 * (s / 16) - 12) * 8)%Z by ring; apply Z_mod_mult).
      apply (pixDestroy_W C A4 M2 _ g3 (s - 96) (s - 96) pixd 0 0 sz (pixv0 w h d 0 data) cmap0 (0x37b18 : word) S ok_C w_M2 sp_g3 al96
               ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) ltac:(rewrite ra_g3; apply bv_eq; reflexivity)
               ltac:(apply ret_ok_even; reflexivity) gp_g3 al8 a0_g3 ltac:(rewrite <- w2l_Z8 by lia; exact slot_M2) px_M2 eq_refl eq_refl eq_refl
               ltac:(rewrite same4; exact lv_pix) lv0_pix).
      * right. unfold pixv0. cbn [p_data]. rewrite same4. split; [exact lv_data|]. split; [exact lv0_data|].
        split; [exact sz_pos|]. split; [exact data_pix|]. intros no; contradiction.
      * left. reflexivity.
      * intros A6 M3 vm6 g4 w_M3 kept_g4 freed post_M3 slot_M3 rt6.
        unfold pixd_post, pixv0 in freed. cbn [p_data] in freed.
        destruct freed as (gone_pix & gone_data & _ & same_else).
        rewrite with_vmmaps_twice in w_M3 |- *.
        assert (room6 : aroom A6 vm6 (kR - RK_deser) (bR - RB_deserT)) by roomT_tac.
        replace (0x37b18 : word) with (Z_to_bv 64 0x37b18) by (apply bv_eq; reflexivity).
        apply (pd_eptr_W C A m md regs s ret S kR bR A6 M3 vm6 g4 0x37b18 0x124ff ok_C kont room6 k_ge b_ge sp_al sp_lo sp_hi
                 ret_good sp_regs w_M3).
        -- apply (POSTM_trans C (c_A0 C) s m M2 M3 post_M2'). apply (POSTM_mono C (c_A0 C) (s - 96 + 8) s M2 M3); [lia | exact post_M3].
        -- intros q. destruct (decide (q = Z_to_bv 64 pixd)) as [-> | q_pix]; [rewrite gone_pix; exact (eq_sym lvA_pix)|].
           destruct (decide (q = Z_to_bv 64 data)) as [-> | q_data]; [rewrite (gone_data ltac:(lia)); exact (eq_sym lvA_data)|].
           rewrite (same_else q q_pix (fun _ => q_data) (fun no => False_ind _ (no eq_refl))), same4.
           exact (others_v q q_pix q_data (fun no => False_ind _ (no eq_refl))).
        -- apply (cells_frm C (s - 96 + 8) M2 M3 s ret (svr regs) ok_C (proj1 post_M3)); first [exact frame_M2 | lia].
        -- csr. reflexivity.
        -- intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity.
        -- unfold ej_leaves. cbn [In]. right. left. reflexivity.
    + destruct cnew as (cm_lo & cm_top & cm16 & arr_lo & arr_top & arr16 & cm_arr & lv3_cm & lv3_arr & lv0_cm & lv0_arr &
                        lv4_cm & lv4_arr & same4 & cmap_M2).
      set (cv := CMAPV arr (cdepth nc) (2 ^ cdepth nc) nc 0) in *.
      pose proof (cdepth_fits nc nc_pos) as (fits & pow_rng).
      pose proof cmap_M2 as (_ & cm_hi & cwf & _).
      pose proof (cf_arr cv cwf) as arr_rng. cbn [c_arr cv] in arr_rng.
      assert (pix_cm : Z_to_bv 64 pixd <> Z_to_bv 64 cm) by (intros e; rewrite e in lv_pix; congruence).
      assert (pix_arr : Z_to_bv 64 pixd <> Z_to_bv 64 arr) by (intros e; rewrite e in lv_pix; congruence).
      assert (data_cm : Z_to_bv 64 data <> Z_to_bv 64 cm) by (intros e; rewrite e in lv_data; congruence).
      assert (data_arr : Z_to_bv 64 data <> Z_to_bv 64 arr) by (intros e; rewrite e in lv_data; congruence).
      assert (lv4_pix : live A4 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (same4 _ pix_cm pix_arr); exact lv_pix).
      assert (lv4_data : live A4 (Z_to_bv 64 data) = Some sz) by (rewrite (same4 _ data_cm data_arr); exact lv_data).
      assert (cmok : cmap_ok cv).
      { unfold cmap_ok. cbn [c_d c_nalloc c_n c_arr cv]. split; [exact (cdepth_cases nc)|]. split; [reflexivity|]. lia. }
      destruct (pd_J1 al_rom g2 M2 s cm pixd (proj1 s_rng) (proj2 s_rng) ltac:(lia) ltac:(lia) slot_M2 sp_g2 a0_g2)
        as (g3 & run3 & a0_g3 & a1_g3 & s1_g3 & ra_g3 & agr3).
      pose proof (w_pure _ _ _ _ w_M2) as pure4.
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure4) (mp_lazy _ pure4) run3).
      assert (sp_g3 : getr g3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      apply (pixSetColormap_W C (c_A0 C) A4 M2 _ g3 (s - 96) pixd cm (pixv0 w h d 0 data) cv (0x37a24 : word) S ok_C w_M2
               (W_sub0 _ _ _ _ w_M2) sp_g3 al96 ltac:(lia) ltac:(lia) ltac:(rewrite ra_g3; apply bv_eq; reflexivity)
               ltac:(apply ret_ok_even; reflexivity) a0_g3 a1_g3 px_M2 eq_refl lv4_pix lv0_pix lv0_pix cmap_M2 cmok lv4_cm pix_cm).
      intros M3 g4 w_M3 kept_g4 post_M3 px_M3 cmap_M3 a0_g4.
      assert (slot_M3 : rdn RSEGS M3 (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd))).
      { rewrite (FRM_rdn16 C (s - 96) M2 M3 (s - 96) 8 ok_C (proj1 post_M3)) by lia. exact slot_M2. }
      assert (sp_g4 : getr g4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      destruct (pd_K al_rom g4 M3 s pixd (proj1 s_rng) (proj2 s_rng) ltac:(lia) slot_M3 sp_g4 a0_g4) as (g5 & run5 & a0_g5 & agr5).
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure4) (mp_lazy _ pure4) run5).
      destruct (pd_GD al_rom g5 M3 pixd dp nc sz (set_cmap (pixv0 w h d 0 data) cm) px_M3 ltac:(lia) pix8 nc_rng ltac:(lia) ltac:(lia)
                  dp_al data4 a0_g5 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (g6 & run6 & a0_g6 & a1_g6 & a2_g6 & ra_g6 & s2_g6 & agr6).
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure4) (mp_lazy _ pure4) run6).
      assert (frame_M3 : cellsZ M3 (frame9 s ret (svr regs))).
      { apply (cells_frm C (s - 96) M2 M3 s ret (svr regs) ok_C (proj1 post_M3)); first [exact frame_M2 | lia]. }
      assert (post_M3' : POSTM C (c_A0 C) s m M3).
      { apply (POSTM_trans C (c_A0 C) s m M2 M3 post_M2'). apply (POSTM_mono C (c_A0 C) (s - 96) s M2 M3); [lia | exact post_M3]. }
      assert (cm_Z : cm <> pixd /\ arr <> pixd /\ data <> cm /\ data <> arr).
      { split; [intros e; apply pix_cm; rewrite e; reflexivity|]. split; [intros e; apply pix_arr; rewrite e; reflexivity|].
        split; [intros e; apply data_cm; rewrite e; reflexivity | intros e; apply data_arr; rewrite e; reflexivity]. }
      assert (pobj3 : pixobj C A A4 M3 pixd (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 cm data) cv).
      { unfold pixobj. cbn [p_rc p_text p_wpl p_h p_data p_cmap c_arr c_nalloc cv].
        split; [exact px_M3|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact sz_pos|].
        split; [exact lv4_pix|]. split; [exact lvA_pix|]. split; [exact lv0_pix|]. split; [exact lv4_data|].
        split; [exact lvA_data|]. split; [exact lv0_data|]. split; [exact data_pix|].
        split.
        - right. split; [lia|]. split; [exact cmap_M3|]. split; [exact lv4_cm|]. split; [exact lv4_arr|]. split; [lia|].
          assert (cm_ne : Z_to_bv 64 cm <> Z_to_bv 64 pixd /\ Z_to_bv 64 cm <> Z_to_bv 64 data) by (split; congruence).
          assert (arr_ne : Z_to_bv 64 arr <> Z_to_bv 64 pixd /\ Z_to_bv 64 arr <> Z_to_bv 64 data) by (split; congruence).
          split; [rewrite <- (others_v _ (proj1 cm_ne) (proj2 cm_ne) (fun no => False_ind _ (no eq_refl))); exact lv3_cm|].
          split; [rewrite <- (others_v _ (proj1 arr_ne) (proj2 arr_ne) (fun no => False_ind _ (no eq_refl))); exact lv3_arr|].
          split; [exact lv0_cm|]. split; [exact lv0_arr|]. split; [exact cm_arr|]. tauto.
        - intros q q_pix q_data q_cmap. destruct (q_cmap ltac:(lia)) as [q_cm q_arr].
          rewrite (same4 q q_cm q_arr). exact (others_v q q_pix q_data (fun no => False_ind _ (no eq_refl))). }
      apply (pd_copy_W C A m md regs s ret S kR bR A4 M3 vm4 g6 dp pl nc w h d pixd data cm cv ok_C kont
               ltac:(roomT_tac) k_ge b_ge sp_al sp_lo sp_hi ret_good sp_regs pay nc_rng len_pl hdr w_pos h_pos w_M3 post_M3' pobj3
               ltac:(split; intros; lia) (fun _ => cmok) frame_M3 slot_M3
               ltac:(csr; reflexivity) ltac:(unfold pd_rest; intros x x_in; destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity)
               a0_g6 a1_g6 a2_g6 ra_g6 ltac:(csr; reflexivity) ltac:(csr; reflexivity) gp_regs).
Qed.


(* [comment removed for export] *)
Lemma pd_hdr_W : forall C A m md regs (s : Z) (ret : word) (S : TSet) (kR bR : Z) A1 M vm1 r (dp : Z) pl (nc wr hr dr ir : Z),
  Cok C -> DKT C A m md regs s ret S kR bR ->
  aroom A1 vm1 (kR - RK_hdr) (bR - RB_hdrT) -> (RK_deser <= kR)%Z -> (RB_deserT <= bR)%Z ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x56270 ->
  payload C dp pl -> let nb := Z.of_nat (length pl) in
  (28 <= nb < 2 ^ 26)%Z -> (0 <= nc <= 256)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z -> (0 <= dr < 2 ^ 32)%Z ->
  bytes_le_to_Z (firstn 4 (skipn (Z.to_nat (4 * nc + 24)) pl)) = ir ->
  W C A1 M (with_vmmaps vm1 md) -> POSTM C (c_A0 C) s m M ->
  cellsZ M (frame9 s ret (svr regs)) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> (forall x, In x pd_rest -> getr r x = getr regs x) ->
  getr r 22 = Z_to_bv 64 nc -> getr r 20 = Z_to_bv 64 nb -> getr r 23 = Z_to_bv 64 dp -> getr r 18 = Z_to_bv 64 hr -> getr r 9 = Z_to_bv 64 wr ->
  getr r 19 = Z_to_bv 64 (zx (sw32 dr)) -> (dp mod 4 = 0)%Z ->
  ((getr r 10 = Z_to_bv 64 0 /\ forall q, live A1 q = live A q)
   \/ (exists pix1, getr r 10 = Z_to_bv 64 pix1 /\ (hdr_ok wr hr (zx (sw32 dr)) /\ pix_new C A A1 M pix1 (pix_hdr wr hr (zx (sw32 dr)))))) ->
  realizes SEGS (mkCfg (mkst r (0x3797c : word) M al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros C A m md regs s ret S kR bR A1 M vm1 r dp pl nc wr hr dr ir ok_C kont room1 k_ge b_ge sp_al sp_lo sp_hi
    ret_good sp_regs gp_regs pay nb nb_rng nc_rng nc_room wr_rng hr_rng area dr_rng ir_def w_M post_M frame_M sp_r rest_r
    s6_r s4_r s7_r s2_r s1_r s3_r dp_al made.
  unfold pd_rest in rest_r. subst nb.
  pose proof (w_pure _ _ _ _ w_M) as pure1.
  pose proof (ck_img C ok_C) as img_lo. cbn [ll_img LLU16 snd] in img_lo.
  pose proof (ck_top C ok_C) as top_lo. pose proof (ck_sp0 C ok_C) as top_sp0. pose proof (ck_sp0hi C ok_C) as sp0_hi.
  pose proof LSTK_val as lstk. assert (lsf : LSF = 3376%Z) by reflexivity.
  pose proof (alloc_top_lt (c_vm C)) as top64. unfold two_pow_64 in top64.
  assert (s_rng : (96 <= s < 2 ^ 64)%Z) by lia.
  assert (s16 : s = (16 * (s / 16))%Z) by (pose proof (Z.div_mod s 16 ltac:(lia)); lia).
  assert (al96 : ((s - 96) mod 16 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 96)%Z with ((s / 16 - 6) * 16)%Z by ring; apply Z_mod_mult).
  pose proof (zx_range (sw32 dr)) as d_rng.
  pose proof (W_sub0 _ _ _ _ w_M) as sub1.
  destruct (payload_live C A1 M _ dp pl ok_C w_M pay ltac:(lia)) as (lv_dp & dp_lo & dp_top).
  pose proof (W_sok_win C A1 M _ (s - 96) 96 ok_C w_M ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as sok.
  destruct made as [(a0_r & same1) | (pix1 & a0_r & hdr1 & fresh1)].
  - destruct (pd_G0 al_rom r M s (proj1 s_rng) (proj2 s_rng) sok sp_r a0_r) as (g1 & run1 & agr1).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run1).
    set (M1 := wbytes M (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
    assert (wp1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) s m M1).
    { apply (WP_win C A1 (c_A0 C) m M _ (Z_to_bv 64 (s - 88)) _ s ok_C (conj w_M post_M) sub1);
        rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (out_M1 : forall x : word, ~ (s - 88 <= u x < s - 80)%Z -> M1 x = M x).
    { intros x x_out. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    replace (0x37a80 : word) with (Z_to_bv 64 0x37a80) by (apply bv_eq; reflexivity).
    apply (pd_tail_W C A m md regs s ret S kR bR A1 M1 vm1 g1 0x37a80 0x10bb4 ok_C kont ltac:(roomT_tac) k_ge b_ge
             sp_al sp_lo sp_hi ret_good sp_regs (proj1 wp1) (proj2 wp1) same1).
    + apply (cells_out M M1 (s - 88) (s - 80) s ret (svr regs) out_M1); first [exact frame_M | lia].
    + csr. reflexivity.
    + intros x x_in. csr. exact (rest_r x x_in).
    + unfold et_leaves. cbn [In]. do 5 right. left. reflexivity.
  - set (dd := zx (sw32 dr)) in *.
    set (sz := (4 * (wpl_of wr dd * hr))%Z) in *.
    pose proof hdr1 as (dval_dd & wr_hi & hr_hi & sz_hi).
    pose proof (wpl_of_range wr dd wr_rng dval_dd) as wpl_rng.
    destruct fresh1 as (pix_lo & pix_top & pix16 & lvA_pix & lv0_pix & lv1_pix & same1 & px_M).
    assert (pix8 : (pix1 mod 8 = 0)%Z).
    { replace pix1 with (16 * (pix1 / 16))%Z by (pose proof (Z.div_mod pix1 16 ltac:(lia)); lia).
      replace (16 * (pix1 / 16))%Z with ((2 * (pix1 / 16)) * 8)%Z by ring. apply Z_mod_mult. }
    pose proof (payload_at C A1 M _ dp pl w_M pay) as bytes_M.
    pose proof pay as (_ & _ & dp_one & dp_hi).
    destruct (payload_field M dp pl (Z.to_nat (4 * nc + 24)) bytes_M dp_one dp_hi ltac:(lia)) as [rd_ir ir_rng].
    rewrite Z2Nat.id in rd_ir by lia. rewrite ir_def in ir_rng.
    destruct (pd_G al_rom r M s dp (Z.of_nat (length pl)) nc pix1 (wpl_of wr dd) hr ir (pix_hdr wr hr dd) _ (proj1 s_rng) (proj2 s_rng) sok px_M
                ltac:(lia) ltac:(lia) pix8 eq_refl hr_rng ltac:(lia) sz_hi nc_rng ltac:(lia) nc_room dp_one ltac:(lia) dp_al
                ltac:(replace (dp + 4 * nc + 24)%Z with (dp + (4 * nc + 24))%Z by ring; exact rd_ir) ir_def ir_rng
                sp_r a0_r s6_r s4_r s7_r s2_r)
      as (g1 & run1 & sp_g1 & a0_g1 & ra_g1 & s4_g1 & s0_g1 & s5_g1 & agr1).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure1) (mp_lazy _ pure1) run1).
    set (M1 := wbytes M (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))).
    assert (wp1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C (c_A0 C) s m M1).
    { apply (WP_win C A1 (c_A0 C) m M _ (Z_to_bv 64 (s - 88)) _ s ok_C (conj w_M post_M) sub1);
        rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    destruct wp1 as [w_M1 post_M1].
    assert (out_M1 : forall x : word, ~ (s - 88 <= u x < s - 80)%Z -> M1 x = M x).
    { intros x x_out. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
    assert (frame_M1 : cellsZ M1 (frame9 s ret (svr regs))).
    { apply (cells_out M M1 (s - 88) (s - 80) s ret (svr regs) out_M1); first [exact frame_M | lia]. }
    assert (px_M1 : PIXat M1 pix1 (pix_hdr wr hr dd)).
    { apply PIXat_out; [exact px_M | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                       | rewrite u_Z2bv by lia; lia]. }
    assert (gp_g1 : getr g1 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
    assert (al88 : ((s - 88) mod 8 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 88)%Z with ((2 * (s / 16) - 11) * 8)%Z by ring; apply Z_mod_mult).
    apply (pixDestroy_W C A1 M1 _ g1 (s - 96) (s - 88) pix1 0 0 0 (pix_hdr wr hr dd) cmap0 (0x379d0 : word) S ok_C w_M1 sp_g1 al96
             ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia) ltac:(rewrite ra_g1; apply bv_eq; reflexivity)
             ltac:(apply ret_ok_even; reflexivity) gp_g1 al88 a0_g1
             ltac:(rewrite <- w2l_Z8 by lia; apply rdn_wbytes_hit8; rewrite u_Z2bv by lia; lia)
             px_M1 eq_refl eq_refl eq_refl lv1_pix lv0_pix (or_introl eq_refl) (or_introl eq_refl)).
    intros A2 M2 vm2 g2 w_M2 kept_g2 freed post_M2 slot_M2 rt2.
    unfold pixd_post in freed. destruct freed as (gone_pix & _ & _ & same_else).
    assert (same2 : forall q : word, live A2 q = live A q).
    { intros q. destruct (decide (q = Z_to_bv 64 pix1)) as [-> | q_pix]; [rewrite gone_pix; exact (eq_sym lvA_pix)|].
      rewrite (same_else q q_pix (fun no => False_ind _ (no eq_refl)) (fun no => False_ind _ (no eq_refl))). exact (same1 q q_pix). }
    rewrite with_vmmaps_twice in w_M2 |- *.
    pose proof (w_pure _ _ _ _ w_M2) as pure2.
    assert (frame_M2 : cellsZ M2 (frame9 s ret (svr regs))).
    { apply (cells_frm C (s - 88 + 8) M1 M2 s ret (svr regs) ok_C (proj1 post_M2)); first [exact frame_M1 | lia]. }
    assert (post_M2' : POSTM C (c_A0 C) s m M2).
    { apply (POSTM_trans C (c_A0 C) s m M1 M2 post_M1). apply (POSTM_mono C (c_A0 C) (s - 88 + 8) s M1 M2); [lia | exact post_M2]. }
    assert (sp_g2 : getr g2 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    assert (ir_box : (0 <= zx (sw32 ir) < 2 ^ 64)%Z) by apply zx_range.
    assert (sizes : (sz = Z.of_nat (length pl) - 4 * nc - 28 /\ sz = zx (sw32 ir))%Z \/
                    (sz <> Z.of_nat (length pl) - 4 * nc - 28 \/ sz <> zx (sw32 ir))%Z).
    { destruct (Z.eq_dec sz (Z.of_nat (length pl) - 4 * nc - 28)); destruct (Z.eq_dec sz (zx (sw32 ir))); tauto. }
    destruct sizes as [(sz_m & sz_i) | mismatch].
    + destruct (pd_H al_rom g2 M2 sz wr hr dd ltac:(lia) ltac:(csr; reflexivity) ltac:(csr; rewrite <- sz_m; reflexivity)
                  ltac:(csr; rewrite <- sz_i; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (g3 & run3 & a0_g3 & a1_g3 & a2_g3 & ra_g3 & agr3).
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure2) (mp_lazy _ pure2) run3).
      assert (sp_g3 : getr g3 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      assert (gp_g3 : getr g3 4 = Z_to_bv 64 0x56270) by (csr; reflexivity).
      apply (pixCreate_szT2_W C A2 M2 _ g3 (s - 96) wr hr dd (0x379e8 : word) S ok_C w_M2 sp_g3 al96 ltac:(lia) ltac:(lia)
               ltac:(rewrite ra_g3; apply bv_eq; reflexivity) ltac:(apply ret_ok_even; reflexivity) gp_g3 a0_g3 a1_g3 a2_g3
               wr_rng hr_rng area d_rng).
      intros A3 M3 vm3 g4 w_M3 kept_g4 post_M3 created rt3.
      rewrite with_vmmaps_twice in w_M3 |- *.
      pose proof (w_pure _ _ _ _ w_M3) as pure3.
      assert (frame_M3 : cellsZ M3 (frame9 s ret (svr regs))).
      { apply (cells_frm C (s - 96) M2 M3 s ret (svr regs) ok_C (proj1 post_M3)); first [exact frame_M2 | lia]. }
      assert (post_M3' : POSTM C (c_A0 C) s m M3).
      { apply (POSTM_trans C (c_A0 C) s m M2 M3 post_M2'). apply (POSTM_mono C (c_A0 C) (s - 96) s M2 M3); [lia|].
        exact (POSTM_sub C (c_A0 C) A2 (s - 96) M2 M3 (W_sub0 _ _ _ _ w_M2) post_M3). }
      assert (sp_g4 : getr g4 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
      destruct created as [(a0_g4 & same3) | (pix & data & a0_g4 & hdr2 & made3)].
      * pose proof (W_sok_win C A3 M3 _ (s - 96) 96 ok_C w_M3 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as sok3.
        destruct (pd_I0 al_rom g4 M3 s (proj1 s_rng) (proj2 s_rng) sok3 sp_g4 a0_g4) as (g5 & run5 & agr5).
        apply (rz_msteps _ _ _ _ _ (mp_halted _ pure3) (mp_lazy _ pure3) run5).
        set (M4 := wbytes M3 (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))).
        assert (wp4 : W C A3 M4 (with_vmmaps vm3 md) /\ POSTM C (c_A0 C) s m M4).
        { apply (WP_win C A3 (c_A0 C) m M3 _ (Z_to_bv 64 (s - 96)) _ s ok_C (conj w_M3 post_M3') (W_sub0 _ _ _ _ w_M3));
            rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
        assert (out_M4 : forall x : word, ~ (s - 96 <= u x < s - 88)%Z -> M4 x = M3 x).
        { intros x x_out. apply wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia. }
        replace (0x37ae0 : word) with (Z_to_bv 64 0x37ae0) by (apply bv_eq; reflexivity).
        apply (pd_eptr_W C A m md regs s ret S kR bR A3 M4 vm3 g5 0x37ae0 0x119a6 ok_C kont ltac:(roomT_tac) k_ge b_ge
                 sp_al sp_lo sp_hi ret_good sp_regs (proj1 wp4) (proj2 wp4) (fun q => eq_trans (same3 q) (same2 q))).
        -- apply (cells_out M3 M4 (s - 96) (s - 88) s ret (svr regs) out_M4); first [exact frame_M3 | lia].
        -- csr. reflexivity.
        -- intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity.
        -- unfold ej_leaves. cbn [In]. left. reflexivity.
      * destruct made3 as (pix_lo2 & pix_top2 & pix16b & data_lo & data_top & data16 & pix_data & lvA2_pix & lvA2_data &
                           lv0_pix2 & lv0_data & lv3_pix & lv3_data & same3 & px_M3 & data_eq).
        assert (pobj3 : pixobj C A A3 M3 pix (pixv0 wr hr dd 0 data) cmap0).
        { unfold pixobj, pixv0. cbn [p_rc p_text p_wpl p_h p_data p_cmap].
          split; [exact px_M3|]. split; [reflexivity|]. split; [reflexivity|].
          split; [apply Z.mul_pos_pos; [lia | apply Z.mul_pos_pos; lia]|].
          split; [exact lv3_pix|]. split; [rewrite <- (same2 _); exact lvA2_pix|]. split; [exact lv0_pix2|].
          split; [exact lv3_data|]. split; [rewrite <- (same2 _); exact lvA2_data|]. split; [exact lv0_data|].
          split; [intros e; apply pix_data; symmetry; exact e|]. split; [left; reflexivity|].
          intros q q_pix q_data _. rewrite (same3 q q_pix q_data). apply same2. }
        apply (pd_created_W C A m md regs s ret S kR bR A3 M3 vm3 g4 dp pl nc wr hr dd pix data ok_C kont ltac:(roomT_tac)
                 k_ge b_ge sp_al sp_lo sp_hi ret_good sp_regs gp_regs pay nc_rng ltac:(lia) hdr2 ltac:(lia) ltac:(lia) w_M3 post_M3'
                 pobj3 frame_M3 sp_g4 ltac:(unfold pd_rest; intros x x_in; destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity)
                 a0_g4 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) dp_al).
    + destruct (pd_Hbad al_rom g2 M2 sz (Z.of_nat (length pl) - 4 * nc - 28) (zx (sw32 ir)) ltac:(lia) ltac:(lia) ir_box mismatch
                  (W_sev_got C A2 M2 _ w_M2) (W_sev C A2 M2 _ w_M2) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
        as (g3 & run3 & a0_g3 & a1_g3 & ra_g3 & agr3).
      apply (rz_msteps _ _ _ _ _ (mp_halted _ pure2) (mp_lazy _ pure2) run3).
      apply (pd_lerr_W C A m md regs s ret S kR bR A2 M2 vm2 g3 0x10e9c 0x37adc 83 ok_C kont ltac:(roomT_tac) k_ge b_ge
               sp_al sp_lo sp_hi ret_good sp_regs w_M2 post_M2' same2 frame_M2 ltac:(csr; reflexivity)
               ltac:(intros x x_in; destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity)
               a0_g3 a1_g3 ra_g3 (or_intror eq_refl) ltac:(apply fmts1_16; cbn [In]; do 3 right; left; reflexivity) str_e8).
Qed.

Theorem pixDeserialize_T_W : forall C A m md regs (s dp : Z) (pl : list byte) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 256 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 ->
  getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length pl)) ->
  payload C dp pl -> (3 <= Z.of_nat (length pl) < 2 ^ 26)%Z -> (dp mod 4 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_deser <= kR)%Z -> (RB_deserT <= bR)%Z ->
  DKT C A m md regs s ret S kR bR ->
  realizes SEGS (mkCfg (mkst regs (0x3771c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s dp pl ret S ok_C w_m sp_regs sp_al sp_lo sp_hi ra_regs ret_good gp_regs a0_regs a1_regs pay nb_rng dp_al
    kR bR room0 k_ge b_ge kont.
  pose proof (w_pure _ _ _ _ w_m) as pure0.
  pose proof (ck_img C ok_C) as img_lo. cbn [ll_img LLU16 snd] in img_lo.
  pose proof (ck_top C ok_C) as top_lo. pose proof (ck_sp0 C ok_C) as top_sp0. pose proof (ck_sp0hi C ok_C) as sp0_hi.
  pose proof LSTK_val as lstk. assert (lsf : LSF = 3376%Z) by reflexivity.
  assert (s_rng : (96 <= s < 2 ^ 64)%Z) by lia.
  assert (s16 : s = (16 * (s / 16))%Z) by (pose proof (Z.div_mod s 16 ltac:(lia)); lia).
  assert (al96 : ((s - 96) mod 16 = 0)%Z) by (rewrite s16; replace (16 * (s / 16) - 96)%Z with ((s / 16 - 6) * 16)%Z by ring; apply Z_mod_mult).
  pose proof pay as (_ & _ & dp_one & dp_hi).
  set (nb := Z.of_nat (length pl)) in *.
  pose proof (W_sok_win C A m md (s - 96) 96 ok_C w_m ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as sok.
  destruct (pd_A0 al_rom regs m s dp nb ret (proj1 s_rng) (proj2 s_rng) ltac:(lia) ltac:(lia) sok sp_regs ra_regs a0_regs a1_regs)
    as (g1 & run1 & sp_g1 & a0_g1 & a1_g1 & a2_g1 & a3_g1 & agr1).
  apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run1).
  set (M0 := FR9 m s ret regs).
  assert (wp0 : W C A M0 md /\ POSTM C (c_A0 C) s m M0) by (unfold M0, FR9; wp_win ok_C).
  destruct wp0 as [w_M0 post_M0].
  assert (w_M0' : W C A M0 (with_vmmaps (m_vmmaps md) md)) by (rewrite with_vmmaps_same; exact w_M0).
  pose proof (cells_FR9 m s ret regs (proj1 s_rng) (proj2 s_rng)) as frame_M0. fold M0 in frame_M0.
  assert (room0' : aroom A (m_vmmaps md) (kR - RK_deser) (bR - RB_deserT)) by roomT_tac.
  assert (rest_g1 : forall x : reg, In x pd_rest -> getr g1 x = getr regs x).
  { unfold pd_rest. intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity. }
  assert (to_tail : forall (g : bvmap 5 word) (pc msg : Z), In (pc, msg) et_leaves -> getr g 2 = Z_to_bv 64 (s - 96) ->
            (forall x : reg, In x pd_rest -> getr g x = getr regs x) -> realizes RSEGS (mkCfg (mkst g (Z_to_bv 64 pc) M0 al_rom) md) S).
  { intros g pc msg leaf sp_g rest_g. rewrite <- (with_vmmaps_same md).
    exact (pd_tail_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) g pc msg ok_C kont room0' k_ge b_ge sp_al sp_lo sp_hi ret_good
             sp_regs w_M0' post_M0 (fun q => eq_refl) frame_M0 sp_g rest_g leaf). }
  unfold pd_rest in rest_g1.
  destruct (Z_lt_ge_dec nb 28) as [short | long].
  - destruct (pd_A2 al_rom g1 M0 nb ltac:(lia) a2_g1 a3_g1 a1_g1 (W_sev_got C A M0 md w_M0) (W_sev C A M0 md w_M0))
      as (g2 & run2 & a0_g2 & a1_g2 & a2_g2 & ra_g2 & agr2).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run2).
    rewrite <- (with_vmmaps_same md).
    apply (pd_lerr_W C A m md regs s ret S kR bR A M0 (m_vmmaps md) g2 0x115a1 0x37788 34 ok_C kont room0' k_ge b_ge sp_al sp_lo sp_hi
             ret_good sp_regs w_M0' post_M0 (fun q => eq_refl) frame_M0 ltac:(csr; reflexivity)
             ltac:(unfold pd_rest; intros x x_in; destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity)
             a0_g2 a1_g2 ra_g2 (or_introl eq_refl) ltac:(apply fmts1_16; cbn [In]; do 9 right; left; reflexivity) str_e1).
  - destruct (pd_A1 al_rom g1 M0 nb ltac:(lia) a2_g1 a3_g1) as (g2 & run2 & agr2).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run2).
    pose proof (payload_at C A M0 md dp pl w_M0 pay) as bytes_M0.
    pose proof (payload_byte M0 dp pl 0 bytes_M0 dp_one dp_hi ltac:(lia)) as rd_b0.
    pose proof (payload_byte M0 dp pl 1 bytes_M0 dp_one dp_hi ltac:(lia)) as rd_b1.
    pose proof (payload_byte M0 dp pl 2 bytes_M0 dp_one dp_hi ltac:(lia)) as rd_b2.
    pose proof (payload_byte M0 dp pl 3 bytes_M0 dp_one dp_hi ltac:(lia)) as rd_b3.
    change (Z.of_nat 0) with 0%Z in rd_b0. rewrite Z.add_0_r in rd_b0.
    change (Z.of_nat 1) with 1%Z in rd_b1. change (Z.of_nat 2) with 2%Z in rd_b2. change (Z.of_nat 3) with 3%Z in rd_b3.
    assert (a0_g2 : getr g2 10 = Z_to_bv 64 dp) by (csr; reflexivity).
    set (b0 := nth 0 pl (Z_to_bv 8 0)) in *. set (b1 := nth 1 pl (Z_to_bv 8 0)) in *.
    set (b2 := nth 2 pl (Z_to_bv 8 0)) in *. set (b3 := nth 3 pl (Z_to_bv 8 0)) in *.
    destruct (decide (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z) as [(m0 & m1 & m2 & m3) | no_magic].
    2: { destruct (pd_Bbad al_rom g2 M0 dp b0 b1 b2 b3 dp_one ltac:(lia) rd_b0 rd_b1 rd_b2 rd_b3 no_magic a0_g2) as (g3 & run3 & agr3).
         apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run3).
         replace (0x37888 : word) with (Z_to_bv 64 0x37888) by (apply bv_eq; reflexivity).
         apply (to_tail g3 0x37888%Z 0x115c4%Z); [unfold et_leaves; cbn [In]; left; reflexivity | csr; reflexivity |].
         unfold pd_rest. intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity. }
    destruct (pd_B al_rom g2 M0 dp b0 b1 b2 b3 dp_one ltac:(lia) dp_al rd_b0 rd_b1 rd_b2 rd_b3 m0 m1 m2 m3 a0_g2)
      as (g3 & run3 & a2_g3 & a3_g3 & agr3).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run3).
    destruct (payload_field M0 dp pl 4 bytes_M0 dp_one dp_hi ltac:(lia)) as [rd_w w_box].
    destruct (payload_field M0 dp pl 8 bytes_M0 dp_one dp_hi ltac:(lia)) as [rd_h h_box].
    destruct (payload_field M0 dp pl 12 bytes_M0 dp_one dp_hi ltac:(lia)) as [rd_d d_box].
    destruct (payload_field M0 dp pl 20 bytes_M0 dp_one dp_hi ltac:(lia)) as [rd_n n_box].
    change (Z.of_nat 4) with 4%Z in rd_w. change (Z.of_nat 8) with 8%Z in rd_h.
    change (Z.of_nat 12) with 12%Z in rd_d. change (Z.of_nat 20) with 20%Z in rd_n.
    set (wr := lez (firstn 4 (skipn 4 pl))) in *. set (hr := lez (firstn 4 (skipn 8 pl))) in *.
    set (dr := lez (firstn 4 (skipn 12 pl))) in *. set (ncr := lez (firstn 4 (skipn 20 pl))) in *.
    assert (a0_g3 : getr g3 10 = Z_to_bv 64 dp) by (csr; reflexivity).
    destruct (decide (1 <= wr <= 1000000)%Z) as [wr_ok | wr_bad].
    2: { destruct (pd_Cbad al_rom g3 M0 dp wr _ dp_one ltac:(lia) rd_w eq_refl w_box wr_bad a0_g3) as (g4 & run4 & agr4).
         apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run4).
         replace (0x37860 : word) with (Z_to_bv 64 0x37860) by (apply bv_eq; reflexivity).
         apply (to_tail g4 0x37860%Z 0x11f8e%Z); [unfold et_leaves; cbn [In]; right; left; reflexivity | csr; reflexivity |].
         unfold pd_rest. intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity. }
    destruct (pd_C al_rom g3 M0 dp wr _ dp_one ltac:(lia) rd_w eq_refl wr_ok a0_g3) as (g4 & run4 & s1_g4 & a3_g4 & agr4).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run4).
    assert (a0_g4 : getr g4 10 = Z_to_bv 64 dp) by (csr; reflexivity).
    destruct (decide (1 <= hr <= 1000000)%Z) as [hr_ok | hr_bad].
    2: { destruct (pd_Dbad al_rom g4 M0 dp hr _ dp_one ltac:(lia) rd_h eq_refl h_box hr_bad a0_g4 a3_g4) as (g5 & run5 & agr5).
         apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run5).
         replace (0x378e8 : word) with (Z_to_bv 64 0x378e8) by (apply bv_eq; reflexivity).
         apply (to_tail g5 0x378e8%Z 0x105b3%Z); [unfold et_leaves; cbn [In]; do 2 right; left; reflexivity | csr; reflexivity |].
         unfold pd_rest. intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity. }
    destruct (pd_D al_rom g4 M0 dp hr _ dp_one ltac:(lia) rd_h eq_refl hr_ok a0_g4 a3_g4) as (g5 & run5 & s2_g5 & agr5).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run5).
    assert (s1_g5 : getr g5 9 = Z_to_bv 64 wr) by (csr; reflexivity).
    destruct (Z_le_gt_dec (wr * hr) 400000000) as [area_ok | area_bad].
    2: { destruct (pd_Ebad al_rom g5 M0 wr hr wr_ok hr_ok ltac:(lia) s1_g5 s2_g5) as (g6 & run6 & agr6).
         apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run6).
         replace (0x37920 : word) with (Z_to_bv 64 0x37920) by (apply bv_eq; reflexivity).
         apply (to_tail g6 0x37920%Z 0x10413%Z); [unfold et_leaves; cbn [In]; do 3 right; left; reflexivity | csr; reflexivity |].
         unfold pd_rest. intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity. }
    destruct (pd_E al_rom g5 M0 wr hr wr_ok hr_ok area_ok s1_g5 s2_g5) as (g6 & run6 & agr6).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run6).
    assert (a0_g6 : getr g6 10 = Z_to_bv 64 dp) by (csr; reflexivity).
    assert (a1_g6 : getr g6 11 = Z_to_bv 64 nb) by (csr; reflexivity).
    assert (a2_g6 : getr g6 12 = Z_to_bv 64 (dp + 20)) by (csr; reflexivity).
    pose proof (Z.mul_div_le nb 4 ltac:(lia)) as quarter.
    destruct (decide (ncr <= 256 /\ ncr + 7 < nb / 4)%Z) as [(nc_hi & nc_room) | nc_bad].
    2: { destruct (pd_Fbad al_rom g6 M0 dp nb ncr (nb / 4) _ dp_one ltac:(lia) ltac:(lia) eq_refl rd_n eq_refl n_box nc_bad
                    a0_g6 a1_g6 a2_g6) as (g7 & run7 & agr7).
         apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run7).
         replace (0x37a58 : word) with (Z_to_bv 64 0x37a58) by (apply bv_eq; reflexivity).
         apply (to_tail g7 0x37a58%Z 0x117ba%Z); [unfold et_leaves; cbn [In]; do 4 right; left; reflexivity | csr; reflexivity |].
         unfold pd_rest. intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity. }
    destruct (pd_F al_rom g6 M0 dp nb ncr (nb / 4) dr wr hr _ _ dp_one ltac:(lia) ltac:(lia) eq_refl rd_n eq_refl ltac:(lia) nc_room
                rd_d eq_refl d_box ltac:(lia) ltac:(lia) a0_g6 a1_g6 a2_g6 ltac:(csr; reflexivity) ltac:(csr; reflexivity))
      as (g7 & run7 & s6_g7 & s4_g7 & s7_g7 & s3_g7 & a0_g7 & a1_g7 & a2_g7 & ra_g7 & agr7).
    apply (rz_msteps _ _ _ _ _ (mp_halted _ pure0) (mp_lazy _ pure0) run7).
    assert (sp_g7 : getr g7 2 = Z_to_bv 64 (s - 96)) by (csr; reflexivity).
    apply (pixCreateHeader_szT2_W C A M0 md g7 (s - 96) wr hr (zx (sw32 dr)) (0x3797c : word) S ok_C w_M0 sp_g7 al96
             ltac:(lia) ltac:(lia) ltac:(rewrite ra_g7; apply bv_eq; reflexivity) ltac:(apply ret_ok_even; reflexivity)
             ltac:(csr; reflexivity) a0_g7 a1_g7 a2_g7 wr_ok hr_ok area_ok (zx_range (sw32 dr))).
    intros A1 M1 vm1 g8 w_M1 kept_g8 post_M1 made rt1.
    apply (pd_hdr_W C A m md regs s ret S kR bR A1 M1 vm1 g8 dp pl ncr wr hr dr (lez (firstn 4 (skipn (Z.to_nat (4 * ncr + 24)) pl)))
             ok_C kont ltac:(roomT_tac) k_ge b_ge sp_al sp_lo sp_hi ret_good sp_regs gp_regs pay ltac:(lia) ltac:(lia) ltac:(lia)
             wr_ok hr_ok area_ok d_box eq_refl w_M1).
    + apply (POSTM_trans C (c_A0 C) s m M0 M1 post_M0). apply (POSTM_mono C (c_A0 C) (s - 96) s M0 M1); [lia|].
      exact (POSTM_sub C (c_A0 C) A (s - 96) M0 M1 (W_sub0 _ _ _ _ w_M0) post_M1).
    + apply (cells_frm C (s - 96) M0 M1 s ret (svr regs) ok_C (proj1 post_M1)); first [exact frame_M0 | lia].
    + csr. reflexivity.
    + unfold pd_rest. intros x x_in. destruct x_in as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; csr; reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + exact dp_al.
    + exact made.
Qed.

End Deser.
