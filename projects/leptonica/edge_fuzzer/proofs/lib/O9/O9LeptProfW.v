(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 LeptScan LeptNuma LeptRoom LeptRoom9.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9LeptStderr O9LeptBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9CL7a.
Import O9CL7a.O9LeptErr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9CL8a.
Import O9CL8a.O9LeptPixHdr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9LeptCmap2 O9LeptPixCopy O9LeptEdge_iface O9LeptScan O9LeptProf.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rok := red; apply bv_eq; reflexivity.

Lemma wpl1_le : forall w, (0 <= w)%Z -> (w <= 32 * wpl_of w 1)%Z.
Proof.
  intros w Hw. unfold wpl_of. rewrite Z.mul_1_r. pose proof (Z.div_mod (w + 31) 32 ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound (w + 31) 32 ltac:(lia)) as R. lia.
Qed.

Section ProfW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O9Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition scan_pre (s pix : Z) (v : pixv) (m0 : word -> option byte) : Prop :=
  (0x20100 <= s)%Z /\ (s < 2 ^ 64)%Z /\ PIXat m0 pix v /\ p_d v = 1%Z /\ (1 <= p_w v)%Z /\ (p_w v <= 32 * p_wpl v)%Z /\ (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z /\
  (p_data v mod 4 = 0)%Z /\ (1 <= p_data v)%Z /\ (4096 <= pix)%Z /\ (pix + 64 <= s - 208)%Z /\ (p_data v + 4 * (p_wpl v * p_h v) <= s - 208)%Z /\
  store_ok SEGS m0 (Z_to_bv 64 (s - 208)) 208 = true /\
  (forall a : word, (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m0 a <> None) /\
  rdn SEGS m0 (Z_to_bv 64 0x1c64c) 4 = Some (Z_to_le_bytes 4 0x46fe0) /\
  rdn SEGS m0 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))).

Lemma W_scan_pre : forall C A m md (s pix w h cm data : Z), Cok C -> W C A m md ->
  (c_top C - LSTK + 208 <= s)%Z -> (s <= c_top C)%Z ->
  PIXat m pix (hdv w h 1 cm data) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 1 * h))%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
  scan_pre s pix (hdv w h 1 cm data) m.
Proof.
  intros C A m md s pix w h cm data CK HW Hlo Hhi PX HOK Hw Hh Lp Ld Rw.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w 1 ltac:(lia) DV) as Hwpl.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd. cbn [p_data hdv] in Rd.
  assert (Rpos : (0 < 4 * (wpl_of w 1 * h))%Z) by (assert (1 * 1 <= wpl_of w 1 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Rpos) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd16 & _). rewrite u_Z2bv in ALd16 by lia.
  unfold scan_pre. cbn [p_d p_w p_h p_wpl p_data hdv].
  split; [lia|]. split; [lia|]. split; [exact PX|]. split; [reflexivity|]. split; [exact Hw|]. split; [apply wpl1_le; lia|].
  split; [change (2 ^ 26)%Z with 67108864%Z; exact Hsz|].
  split; [replace data with (data + 0)%Z by lia; apply mod16_plus_mod4; [exact ALd16 | reflexivity]|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [exact (W_sok_win C A m md (s - 208) 208 CK HW ltac:(lia) ltac:(cbn; lia))|].
  split.
  { intros a Ha. destruct (blk_byte C A m md (Z_to_bv 64 data) _ a CK HW Ld ltac:(rewrite u_Z2bv by lia; exact Ha)) as (_ & D & _). exact D. }
  split; [| exact Rw].
  rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1c64c 4 HW); [rewrite p16_segs; exact jt1_val | |]; cbn [fst snd ll_ro LL16]; lia.
Qed.

(* [comment removed for export] *)
Lemma r0_scan_b : forall (fx : FPState) s pix v m0, scan_pre s pix v m0 -> forall regs,
  (1 <= p_h v)%Z -> getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 21 = Z_to_bv 64 (p_w v) -> getr regs 22 = Z_to_bv 64 1 ->
  exists regs' m' loc, msteps SEGS (mkst regs (0x77f8c : word) m0 al_rom) (mkst regs' (0x78154 : word) m' al_rom)
    /\ sinv s m0 m' /\ (0 <= loc < p_w v)%Z /\ getr regs' 24 = Z_to_bv 64 loc
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 20; 21; 24]%list) regs regs'.
Proof.
  intros fx s pix v m0 (Hs & Hs64 & PX0 & Hd1 & Hw1 & Hw32 & Hsz & ALd & Hdp & Gp & Hpix & Hdat & SOK0 & RDEF & JT0 & RW0) regs Hh H2 H19 H21 H22.
  pose proof PX0 as (_ & _ & WF & _). pose proof (wf_w _ WF) as Rw.
  destruct (r0_scan al_rom s pix v m0 Hs Hs64 PX0 Hd1 Hw1 Hw32 Hsz ALd Hdp Gp Hpix Hdat SOK0 RDEF JT0 RW0 (Z.to_nat (p_w v)) regs m0 (p_w v - 1)%Z
              ltac:(lia) (sinv_refl s m0) ltac:(lia) Hh H2 H19 ltac:(rewrite H21; f_equal; lia) H22) as (r1 & m1 & c' & RUN1 & SI1 & Hc' & V24 & AG1).
  destruct (r0_dec al_rom s pix v m0 Hs Hs64 PX0 Hd1 Hw1 Hw32 Hsz ALd Hdp Gp Hpix Hdat SOK0 RDEF JT0 RW0 r1 m1 c' Hc' V24) as (r2 & RUN2 & W24 & AG2).
  exists r2, m1, (c' - 1)%Z. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact SI1|]. split; [lia|]. split; [exact W24 | ra_chain].
Qed.

Lemma ep_row_b : forall (fx : FPState) s pix v m0, scan_pre s pix v m0 -> forall regs (c y : Z),
  (0 <= c < p_w v)%Z -> (0 <= y < p_h v)%Z ->
  getr regs 2 = Z_to_bv 64 (s - 144) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 23 = Z_to_bv 64 y -> getr regs 24 = Z_to_bv 64 c -> getr regs 26 = Z_to_bv 64 1 ->
  exists regs' m' loc, msteps SEGS (mkst regs (0x781c0 : word) m0 al_rom) (mkst regs' (0x781a8 : word) m' al_rom)
    /\ sinv s m0 m' /\ (0 <= loc < p_w v)%Z /\ getr regs' 24 = Z_to_bv 64 loc
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 24; 25]%list) regs regs'.
Proof.
  intros fx s pix v m0 (Hs & Hs64 & PX0 & Hd1 & Hw1 & Hw32 & Hsz & ALd & Hdp & Gp & Hpix & Hdat & SOK0 & RDEF & JT0 & RW0) regs c y Hc Hy H2 H19 H23 H24 H26.
  exact (ep_row al_rom s pix v m0 Hs Hs64 PX0 Hd1 Hw1 Hw32 Hsz ALd Hdp Gp Hpix Hdat SOK0 RDEF JT0 RW0 regs c y Hc Hy H2 H19 H23 H24 H26).
Qed.

(* [comment removed for export] *)
Lemma sinv_W : forall C A m md (s : Z) m', Cok C -> W C A m md -> (c_top C - LSTK <= s - 208)%Z -> (s <= c_top C)%Z -> sinv s m m' ->
  W C A m' md /\ POSTM C A (s - 104) m m'.
Proof.
  intros C A m md s m' CK HW Hlo Hhi [G E].
  assert (OUT : forall a : word, ~ (s - 208 <= u a < s - 104)%Z -> m' a = m a) by (intros a Ha; apply E; unfold scanR; lia).
  split.
  - apply (W_local C A m md m' (s - 104) CK HW ltac:(lia)); [| exact G].
    intros a NE. left. unfold scratch. destruct (Z_lt_ge_dec (u a) (s - 208)) as [L1|G1]; [exfalso; apply NE; apply OUT; lia|].
    destruct (Z_lt_ge_dec (u a) (s - 104)) as [L2|G2]; [lia | exfalso; apply NE; apply OUT; lia].
  - apply (POSTM_range C A m md m' (s - 208) (s - 104) (s - 104) CK HW OUT); lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Rows.
Hypothesis NAN : numaAddNumber_store_contract.
Variables (C : lctx) (A A1 : AS) (m : word -> option byte) (md1 : Model) (s : Z) (ret : word) (regs : bvmap 5 word) (S : TSet).
Variables (pix w h cm data na arr : Z).
Hypothesis CK : Cok C.
Hypothesis Hs16 : (s mod 16 = 0)%Z.
Hypothesis Hlo : (c_top C - LSTK + GEP_STACK <= s)%Z.
Hypothesis Hhi : (s <= c_top C)%Z.
Hypothesis Hret : ret_ok ret.
Hypothesis H2 : getr regs 2 = Z_to_bv 64 s.
Hypothesis PX : PIXat m pix (hdv w h 1 cm data).
Hypothesis HOK : hdr_ok w h 1.
Hypothesis Hw : (1 <= w)%Z.
Hypothesis Hh : (1 <= h)%Z.
Hypothesis Lp : live A (Z_to_bv 64 pix) = Some 64%Z.
Hypothesis Ld : live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 1 * h))%Z.
Hypothesis SUB : sub_live A A1.
Hypothesis L0n : live A (Z_to_bv 64 na) = None.
Hypothesis L0a : live A (Z_to_bv 64 arr) = None.
(* [comment removed for export] *)
Hypothesis KX : forall (fx' : FPState) mf rr, frm_zero (@fp_csr fx') -> W C A1 mf md1 -> cs_kept regs rr -> POSTM C A s m mf ->
    getr rr 10 = Z_to_bv 64 na -> numa_at C A1 mf na h h arr -> realizes SEGS (mkCfg (@mkst fx' rr ret mf al_rom) md1) S.

(* [comment removed for export] *)
Definition rowst (mk : word -> option byte) : Prop :=
  W C A1 mk md1 /\ POSTM C A s m mk /\ cellsZ mk (frameE s ret regs) /\
  rdn SEGS mk (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS mk (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)).

Lemma stack_facts : (c_top C - LSTK + 1376 <= s)%Z /\ (1376 <= s)%Z /\ (s < 2 ^ 64)%Z.
Proof.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold GEP_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo. lia.
Qed.

Lemma rowst_scan : forall mk, rowst mk -> scan_pre s pix (hdv w h 1 cm data) mk.
Proof.
  intros mk (HWk & PMk & _ & Rw & _). destruct stack_facts as (S1 & S2 & S3).
  pose proof PX as (Hp0 & Hp64 & _).
  apply (W_scan_pre C A1 mk md1 s pix w h cm data CK HWk ltac:(lia) Hhi); [| exact HOK | exact Hw | exact Hh | exact (SUB _ _ Lp) | exact (SUB _ _ Ld) | exact Rw].
  apply (PIXat_frame m); [exact PX|]. intros x Hx. exact (LIVK_at A m mk pix 64 x (proj2 PMk) Lp ltac:(lia) ltac:(lia) Hx).
Qed.

(* [comment removed for export] *)
Lemma add_step : forall (pcF : word) (raR : Z),
  (forall (fx' : FPState) r0 m0 (na0 : Z), frm_zero (@fp_csr fx') -> getr r0 9 = Z_to_bv 64 na0 ->
     exists fr cs r', frm_zero cs /\ msteps SEGS (@mkst fx' r0 pcF m0 al_rom) (@mkst (mkFP fr cs) r' (0x60b90 : word) m0 al_rom)
       /\ getr r' 1 = Z_to_bv 64 raR /\ getr r' 10 = Z_to_bv 64 na0 /\ regs_agree (fun x => In x [1; 10]%list) r0 r') ->
  ret_ok (Z_to_bv 64 raR) ->
  forall (fxk : FPState) mk r (y : Z), frm_zero (@fp_csr fxk) -> rowst mk -> numa_at C A1 mk na h y arr -> (0 <= y < h)%Z ->
  getr r 2 = Z_to_bv 64 (s - 144) -> getr r 9 = Z_to_bv 64 na ->
  (forall (fx' : FPState) m' r', frm_zero (@fp_csr fx') -> rowst m' -> numa_at C A1 m' na h (y + 1) arr -> cs_kept r r' ->
     realizes SEGS (mkCfg (@mkst fx' r' (Z_to_bv 64 raR) m' al_rom) md1) S) ->
  realizes SEGS (mkCfg (@mkst fxk r pcF mk al_rom) md1) S.
Proof using All.
  intros pcF raR SEG ROK fxk mk r y Hz (HWk & PMk & CEk & Rwk & Rhk) NAk Hy Q2 Q9 K.
  destruct stack_facts as (S1 & S2 & S3). pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  destruct (SEG fxk r mk na Hz Q9) as (fr & cs & r1 & Hz1 & RUN1 & E1 & E10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |]. clear RUN1.
  replace (0x60b90 : word) with (Z_to_bv 64 PC_numaAddNumber) by (apply bv_eq; reflexivity).
  apply (NAN (mkFP fr cs) C A A1 mk md1 r1 (s - 144)%Z na h y arr (Z_to_bv 64 raR) S Hz1 CK HWk SUB ltac:(rewrite (AG1 2%bv) by notin_list; exact Q2)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)
           E1 ROK E10 NAk ltac:(lia) L0n L0a).
  intros fx' m' r' Hz' HW' CS' PM' NA' _ _ _.
  apply (K fx' m' r' Hz'); [| exact NA' |].
  - split; [exact HW'|]. split; [eapply POSTM_trans; [exact PMk | eapply POSTM_mono; [| exact PM']; lia]|].
    split; [apply (cellsZ_frm C (s - 144) mk m' _ CK (proj1 PM')); [lia | | exact CEk];
            unfold frameE; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil|].
    split; [rewrite (FRM_rdn16 C (s - 144) mk m' (s - 116) 4 CK (proj1 PM')) by (cbn; lia); exact Rwk
           | rewrite (FRM_rdn16 C (s - 144) mk m' (s - 120) 4 CK (proj1 PM')) by (cbn; lia); exact Rhk].
  - intros x Hx. rewrite (CS' x Hx). apply AG1. cbn [In]. intros [E|[E|[]]]; subst x; unfold AllocIface.callee_saved in Hx;
      (destruct Hx as [X|[X|[X|[X|[X|X]]]]]; [discriminate X | discriminate X | discriminate X | discriminate X | discriminate X | vm_compute in X; destruct X as [X1 X2]; first [exact (X1 eq_refl) | discriminate]]).
Qed.

(* [comment removed for export] *)
Definition rinv (y : Z) : Prop :=
  forall (fxk : FPState) mk r (loc : Z), frm_zero (@fp_csr fxk) -> rowst mk -> numa_at C A1 mk na h y arr -> (0 <= loc < w)%Z ->
    getr r 2 = Z_to_bv 64 (s - 144) -> getr r 8 = Z_to_bv 64 0 -> getr r 9 = Z_to_bv 64 na -> getr r 19 = Z_to_bv 64 pix ->
    getr r 23 = Z_to_bv 64 y -> getr r 24 = Z_to_bv 64 loc -> getr r 26 = Z_to_bv 64 1 -> getr r 3 = getr regs 3 -> getr r 4 = getr regs 4 ->
    realizes SEGS (mkCfg (@mkst fxk r (0x781c0 : word) mk al_rom) md1) S.

Lemma exit_W : forall (fxk : FPState) mk r, frm_zero (@fp_csr fxk) -> rowst mk -> numa_at C A1 mk na h h arr ->
  getr r 2 = Z_to_bv 64 (s - 144) -> getr r 8 = Z_to_bv 64 0 -> getr r 9 = Z_to_bv 64 na -> getr r 3 = getr regs 3 -> getr r 4 = getr regs 4 ->
  realizes SEGS (mkCfg (@mkst fxk r (0x78800 : word) mk al_rom) md1) S.
Proof using All.
  intros fxk mk r Hz (HWk & PMk & CEk & _ & _) NAk Q2 Q8 Q9 Q3 Q4. destruct stack_facts as (S1 & S2 & S3).
  destruct (@ep_Z fxk al_rom r regs mk s na ret ltac:(lia) S3 Hret CEk Q2 Q8 Q9) as (r1 & RUN1 & V2 & V10 & VR & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |].
  apply (KX fxk mk r1 Hz HWk); [| exact PMk | exact V10 | exact NAk].
  apply cs_kept_intro; first [solve [apply VR; in_lit] | (rewrite V2, H2; reflexivity)
                            | (rewrite (AG1 3%bv) by notin_list; exact Q3) | (rewrite (AG1 4%bv) by notin_list; exact Q4)].
Qed.

Lemma row_W : forall y, (1 <= y < h)%Z -> (y + 1 < h -> rinv (y + 1))%Z -> rinv y.
Proof.
  intros y Hy NXT. unfold rinv. intros fxk mk r loc Hz RS NAk Hl Q2 Q8 Q9 Q19 Q23 Q24 Q26 Q3 Q4.
  destruct stack_facts as (S1 & S2 & S3). pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  pose proof HOK as (_ & _ & Hh2 & _).
  pose proof RS as (HWk & PMk & CEk & Rwk & Rhk).
  destruct (@ep_row_b fxk s pix (hdv w h 1 cm data) mk (rowst_scan mk RS) r loc y Hl ltac:(cbn [p_h hdv]; lia) Q2 Q19 Q23 Q24 Q26)
    as (r1 & m1 & loc' & RUN1 & SI1 & Hl' & V24 & AG1). cbn [p_w hdv] in Hl'.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |]. clear RUN1.
  destruct (sinv_W C A1 mk md1 s m1 CK HWk ltac:(lia) Hhi SI1) as [HW1 PM1]. pose proof SI1 as [G1 E1].
  assert (RS1 : rowst m1).
  { split; [exact HW1|]. split; [eapply POSTM_trans; [exact PMk | apply (POSTM_sub C A A1 _ _ _ SUB); eapply POSTM_mono; [| exact PM1]; lia]|].
    split; [apply (cellsZ_keep mk m1); [| exact CEk]; unfold frameE;
            repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros z Hz0; apply E1; unfold scanR; lia]] |]); apply Forall_nil|].
    split; [rewrite <- Rwk | rewrite <- Rhk]; (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply E1; unfold scanR; lia]). }
  assert (NA1 : numa_at C A1 m1 na h y arr) by (apply (numa_at_keep C A1 A1 mk m1); [exact NAk | apply sub_live_refl | exact (proj2 PM1)]).
  apply (add_step (0x781a8 : word) 0x781b4 (fun fx' r0 m0 na0 => @ep_Ck al_rom fx' r0 m0 na0) ltac:(rok) fxk m1 r1 y Hz RS1 NA1 ltac:(lia)).
  { rewrite (AG1 2%bv) by notin_list. exact Q2. }
  { rewrite (AG1 9%bv) by notin_list. exact Q9. }
  intros fx' m' r' Hz' RS' NA' CS'.
  replace (Z_to_bv 64 0x781b4) with (0x781b4 : word) by (apply bv_eq; reflexivity).
  pose proof RS' as (HW' & _ & _ & _ & Rh').
  destruct (@ep_F fx' al_rom r' m' s h y _ ltac:(lia) S3 Hy ltac:(lia) eq_refl Rh') as (r2 & RUN2 & W23 & AG2).
  { rewrite (cs_kept_get _ _ _ CS' cs2), (AG1 2%bv) by notin_list. exact Q2. }
  { rewrite (cs_kept_get _ _ _ CS' cs23), (AG1 23%bv) by notin_list. exact Q23. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]. clear RUN2.
  assert (R2 : getr r2 2 = Z_to_bv 64 (s - 144)) by (rewrite (AG2 2%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs2), (AG1 2%bv) by notin_list; exact Q2).
  assert (R8 : getr r2 8 = Z_to_bv 64 0) by (rewrite (AG2 8%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs8), (AG1 8%bv) by notin_list; exact Q8).
  assert (R9 : getr r2 9 = Z_to_bv 64 na) by (rewrite (AG2 9%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs9), (AG1 9%bv) by notin_list; exact Q9).
  assert (R3 : getr r2 3 = getr regs 3) by (rewrite (AG2 3%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs3), (AG1 3%bv) by notin_list; exact Q3).
  assert (R4 : getr r2 4 = getr regs 4) by (rewrite (AG2 4%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs4), (AG1 4%bv) by notin_list; exact Q4).
  destruct (Z.ltb_spec (y + 1) h) as [LT|GE].
  - apply (NXT LT fx' m' r2 loc' Hz' RS' NA' Hl' R2 R8 R9); [| exact W23 | | | exact R3 | exact R4].
    + rewrite (AG2 19%bv) by notin_list. rewrite (cs_kept_get _ _ _ CS' cs19), (AG1 19%bv) by notin_list. exact Q19.
    + rewrite (AG2 24%bv) by notin_list. rewrite (cs_kept_get _ _ _ CS' cs24). exact V24.
    + rewrite (AG2 26%bv) by notin_list. rewrite (cs_kept_get _ _ _ CS' cs26), (AG1 26%bv) by notin_list. exact Q26.
  - replace (y + 1)%Z with h in NA' by lia.
    exact (exit_W fx' m' r2 Hz' RS' NA' R2 R8 R9 R3 R4).
Qed.

Lemma rows : forall (n : nat) y, (h - y <= Z.of_nat n)%Z -> (1 <= y < h)%Z -> rinv y.
Proof using All.
  induction n as [|n IH]; intros y Hn Hy; [lia|].
  apply (row_W y Hy). intros LT. apply IH; lia.
Qed.

End Rows.
(* [comment removed for export] *)
Theorem pixGetEdgeProfile_W : numaCreate_contract -> numaAddNumber_store_contract -> pixGetEdgeProfile_contract.
Proof.
  intros NCR NAN. unfold pixGetEdgeProfile_contract.
  intros fx C A m md regs s pixs w h cm data ret S Hfz CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PX HOK Hw Hh Lp Ld kR bR Hrm Hrk Hrb HK.
  replace (Z_to_bv 64 PC_pixGetEdgeProfile) with (0x77d90 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (SF : (c_top C - LSTK + 1376 <= s)%Z) by (unfold GEP_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  (* [comment removed for export] *)
  destruct (@ep_A fx al_rom regs m s pixs (hdv w h 1 cm data) ret ltac:(lia) ltac:(lia) PX eq_refl Gp ltac:(lia)
              (W_sok_win C A m md (s - 144) 144 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q18 & Q19 & Q20 & AG1). cbn [p_w p_h hdv] in RUN1, Q10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := DIMS (FRE m s ret regs) (s - 116) (s - 120) w h).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMS, FRE; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (CE1 : cellsZ M1 (frameE s ret regs)) by (subst M1; unfold DIMS, FRE, frameE; cbn [cellsZ]; repeat split; rdn_solve).
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))).
  { subst M1. unfold DIMS. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { subst M1. unfold DIMS. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  (* [comment removed for export] *)
  replace (0x609ec : word) with (Z_to_bv 64 PC_numaCreate) by (apply bv_eq; reflexivity).
  assert (En0 : numa_n0 h = h) by (unfold numa_n0; destruct (Z.leb_spec 1 h), (Z.leb_spec h 100000000); cbn; lia).
  apply (NCR fx C A M1 md r1 (s - 144)%Z h (Z_to_bv 64 0x77ee8) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold NCR_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) Q1 ltac:(rok) ltac:(rewrite (AG1 4%bv) by notin_list; exact H4) Q10 ltac:(lia)
           kR bR Hrm Hrk ltac:(rewrite En0; exact Hrb)).
  rewrite En0.
  intros A1 m2 vm1 r2 na arr HW2 CS2 PM2 A10 (NA2 & L0n & L0a & LEQ) Hrm1.
  replace (Z_to_bv 64 0x77ee8) with (0x77ee8 : word) by (apply bv_eq; reflexivity).
  assert (SUB : sub_live A A1) by (intros q k Lq; rewrite LEQ; [exact Lq | intros E; subst q; congruence | intros E; subst q; congruence]).
  assert (PMa : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM2]; lia]).
  assert (CE2 : cellsZ m2 (frameE s ret regs)).
  { apply (cellsZ_frm C (s - 144) M1 m2 _ CK (proj1 PM2)); [lia | | exact CE1]. unfold frameE. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. }
  assert (Rw2 : rdn SEGS m2 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))) by (rewrite (FRM_rdn16 C (s - 144) M1 m2 (s - 116) 4 CK (proj1 PM2)) by (cbn; lia); exact Rw1).
  assert (Rh2 : rdn SEGS m2 (Z_to_bv 64 (s - 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (rewrite (FRM_rdn16 C (s - 144) M1 m2 (s - 120) 4 CK (proj1 PM2)) by (cbn; lia); exact Rh1).
  assert (PX2 : PIXat m2 pixs (hdv w h 1 cm data)).
  { apply (PIXat_frame m); [exact PX|]. intros x Hx. exact (LIVK_at A m m2 pixs 64 x (proj2 PMa) Lp ltac:(lia) ltac:(lia) Hx). }
  (* [comment removed for export] *)
  destruct (@ep_B fx al_rom r2 m2 s pixs na (hdv w h 1 cm data) ltac:(lia) ltac:(lia) PX2 eq_refl Hw Gp ltac:(lia)
              (W_sok_win C A1 m2 _ (s - 208) 208 CK HW2 ltac:(lia) ltac:(cbn; lia)) Rw2
              ltac:(rewrite (cs_kept_get _ _ _ CS2 cs2); exact Q2) A10 ltac:(rewrite (cs_kept_get _ _ _ CS2 cs18); exact Q18)
              ltac:(rewrite (cs_kept_get _ _ _ CS2 cs19); exact Q19) ltac:(rewrite (cs_kept_get _ _ _ CS2 cs20); exact Q20))
    as (r3 & RUN3 & V9 & V21 & V22 & AG3). cbn [p_w p_h hdv] in RUN3, V21.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. clear RUN3.
  set (M3 := DIMS m2 (s - 136) (s - 108) w h).
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A1 s m2 M3) by (subst M3; unfold DIMS; wp_win CK).
  destruct WP3 as [HW3 PM3].
  assert (OUT3 : forall x : word, ~ (s - 136 <= u x < s - 132)%Z -> ~ (s - 108 <= u x < s - 104)%Z -> M3 x = m2 x).
  { intros x Hx Hx'. subst M3. unfold DIMS. rewrite !wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity. }
  assert (RS3 : rowst C A A1 m (with_vmmaps vm1 md) s ret regs w h M3).
  { split; [exact HW3|]. split; [eapply POSTM_trans; [exact PMa | apply (POSTM_sub C A A1 _ _ _ SUB); exact PM3]|].
    split; [apply (cellsZ_keep m2 M3); [| exact CE2]; unfold frameE;
            repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros z Hz0; apply OUT3; lia]] |]); apply Forall_nil|].
    split; [rewrite <- Rw2 | rewrite <- Rh2]; (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply OUT3; lia]). }
  assert (NA3 : numa_at C A1 M3 na h 0 arr) by (apply (numa_at_keep C A1 A1 m2 M3); [exact NA2 | apply sub_live_refl | exact (proj2 PM3)]).
  assert (R3x : forall x, AllocIface.callee_saved x -> x <> 9%bv -> x <> 20%bv -> x <> 21%bv -> x <> 22%bv -> getr r3 x = getr r1 x).
  { intros x Hx N9 N20 N21 N22. rewrite (AG3 x); [exact (CS2 x Hx)|]. cbn [In]. intros [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]; subst x; try contradiction;
      unfold AllocIface.callee_saved in Hx; (destruct Hx as [X|[X|[X|[X|[X|X]]]]]; [discriminate X | discriminate X | discriminate X | discriminate X | discriminate X | vm_compute in X; destruct X as [X1 X2]; first [exact (X1 eq_refl) | discriminate]]). }
  (* [comment removed for export] *)
  assert (KX : forall (fx' : FPState) mf rr, frm_zero (@fp_csr fx') -> W C A1 mf (with_vmmaps vm1 md) -> cs_kept regs rr -> POSTM C A s m mf ->
             getr rr 10 = Z_to_bv 64 na -> numa_at C A1 mf na h h arr -> realizes SEGS (mkCfg (@mkst fx' rr ret mf al_rom) (with_vmmaps vm1 md)) S).
  { intros fx' mf rr Hz' HWf CSf PMf A10f NAf. exact (HK fx' A1 mf vm1 rr na arr Hz' HWf CSf PMf A10f NAf L0n L0a LEQ Hrm1). }
  (* [comment removed for export] *)
  destruct (@r0_scan_b fx s pixs (hdv w h 1 cm data) M3 (rowst_scan C A A1 m _ s ret regs pixs w h cm data CK Hlo Hhi PX HOK Hw Hh Lp Ld SUB M3 RS3) r3 ltac:(cbn [p_h hdv]; lia)
              ltac:(rewrite (R3x 2%bv cs2) by (intros E; discriminate E); exact Q2) ltac:(rewrite (R3x 19%bv cs19) by (intros E; discriminate E); exact Q19) V21 V22)
    as (r4 & m4 & loc0 & RUN4 & SI4 & Hl0 & W24 & AG4). cbn [p_w hdv] in Hl0.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |]. clear RUN4.
  destruct (sinv_W C A1 M3 _ s m4 CK HW3 ltac:(lia) Hhi SI4) as [HW4 PM4]. pose proof SI4 as [G4 E4].
  assert (RS4 : rowst C A A1 m (with_vmmaps vm1 md) s ret regs w h m4).
  { destruct RS3 as (_ & PMk & CEk & Rwk & Rhk).
    split; [exact HW4|]. split; [eapply POSTM_trans; [exact PMk | apply (POSTM_sub C A A1 _ _ _ SUB); eapply POSTM_mono; [| exact PM4]; lia]|].
    split; [apply (cellsZ_keep M3 m4); [| exact CEk]; unfold frameE;
            repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros z Hz0; apply E4; unfold scanR; lia]] |]); apply Forall_nil|].
    split; [rewrite <- Rwk | rewrite <- Rhk]; (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply E4; unfold scanR; lia]). }
  assert (NA4 : numa_at C A1 m4 na h 0 arr) by (apply (numa_at_keep C A1 A1 M3 m4); [exact NA3 | apply sub_live_refl | exact (proj2 PM4)]).
  assert (R4x : forall x, AllocIface.callee_saved x -> x <> 9%bv -> x <> 20%bv -> x <> 21%bv -> x <> 22%bv -> x <> 24%bv -> getr r4 x = getr r1 x).
  { intros x Hx N9 N20 N21 N22 N24. rewrite (AG4 x); [exact (R3x x Hx N9 N20 N21 N22)|]. cbn [In]. intros [E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]; subst x; try contradiction;
      unfold AllocIface.callee_saved in Hx; (destruct Hx as [X|[X|[X|[X|[X|X]]]]]; [discriminate X | discriminate X | discriminate X | discriminate X | discriminate X | vm_compute in X; destruct X as [X1 X2]; first [exact (X1 eq_refl) | discriminate]]). }
  assert (E9 : getr r4 9 = Z_to_bv 64 na) by (rewrite (AG4 9%bv) by notin_list; exact V9).
  apply (add_step NAN C A A1 m (with_vmmaps vm1 md) s ret regs S pixs w h cm data na arr CK Hs16 Hlo Hhi Hret H2 PX HOK Hw Hh Lp Ld SUB L0n L0a KX
           (0x78154 : word) 0x78160 (fun fx' r0 m0 na0 => @ep_C0 al_rom fx' r0 m0 na0) ltac:(rok) fx m4 r4 0%Z Hfz RS4 NA4 ltac:(lia)
           ltac:(rewrite (R4x 2%bv cs2) by (intros E; discriminate E); exact Q2) E9).
  intros fx' m' r' Hz' RS' NA' CS'. replace (0 + 1)%Z with 1%Z in NA' by lia.
  replace (Z_to_bv 64 0x78160) with (0x78160 : word) by (apply bv_eq; reflexivity).
  pose proof RS' as (HW' & PM' & CE' & Rw' & Rh').
  assert (B2 : getr r' 2 = Z_to_bv 64 (s - 144)) by (rewrite (cs_kept_get _ _ _ CS' cs2), (R4x 2%bv cs2) by (intros E; discriminate E); exact Q2).
  assert (B8 : getr r' 8 = Z_to_bv 64 0) by (rewrite (cs_kept_get _ _ _ CS' cs8), (R4x 8%bv cs8) by (intros E; discriminate E); exact Q8).
  assert (B9 : getr r' 9 = Z_to_bv 64 na) by (rewrite (cs_kept_get _ _ _ CS' cs9); exact E9).
  assert (B19 : getr r' 19 = Z_to_bv 64 pixs) by (rewrite (cs_kept_get _ _ _ CS' cs19), (R4x 19%bv cs19) by (intros E; discriminate E); exact Q19).
  assert (B24 : getr r' 24 = Z_to_bv 64 loc0) by (rewrite (cs_kept_get _ _ _ CS' cs24); exact W24).
  assert (B3 : getr r' 3 = getr regs 3) by (rewrite (cs_kept_get _ _ _ CS' cs3), (R4x 3%bv cs3) by (intros E; discriminate E); apply AG1; notin_list).
  assert (B4 : getr r' 4 = getr regs 4) by (rewrite (cs_kept_get _ _ _ CS' cs4), (R4x 4%bv cs4) by (intros E; discriminate E); apply AG1; notin_list).
  destruct (Z_lt_ge_dec h 2) as [H1'|H2'].
  - (* [comment removed for export] *)
    assert (h = 1)%Z by lia. subst h.
    destruct (@ep_D_exit fx' al_rom r' m' s ltac:(lia) ltac:(lia) Rh' B2) as (r5 & RUN5 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN5 |]. clear RUN5.
    apply (exit_W NAN C A A1 m (with_vmmaps vm1 md) s ret regs S pixs w 1%Z cm data na arr CK Hs16 Hlo Hhi Hret H2 PX HOK Hw Hh Lp Ld SUB L0n L0a KX fx' m' r5 Hz' RS' NA');
      rewrite (AG5 _) by notin_list; assumption.
  - (* [comment removed for export] *)
    destruct (@ep_D_loop fx' al_rom r' m' s h ltac:(lia) ltac:(lia) ltac:(lia) Rh' (W_sev_got C A1 m' _ HW')
                (W_sok_win C A1 m' _ (s - 144) 8 CK HW' ltac:(lia) ltac:(cbn; lia)) B2) as (r5 & RUN5 & V23 & V26 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN5 |]. clear RUN5.
    set (M5 := wbytes m' (Z_to_bv 64 (s - 144)) (word_to_le_bytes 8 (Z_to_bv 64 0x140b6))).
    assert (WP5 : W C A1 M5 (with_vmmaps vm1 md) /\ POSTM C A1 s m' M5) by (subst M5; wp_win CK).
    destruct WP5 as [HW5 PM5].
    assert (OUT5 : forall x : word, ~ (s - 144 <= u x < s - 136)%Z -> M5 x = m' x).
    { intros x Hx. subst M5. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia). reflexivity. }
    assert (RS5 : rowst C A A1 m (with_vmmaps vm1 md) s ret regs w h M5).
    { split; [exact HW5|]. split; [eapply POSTM_trans; [exact PM' | apply (POSTM_sub C A A1 _ _ _ SUB); exact PM5]|].
      split; [apply (cellsZ_out m' M5 (s - 144) (s - 136) _ OUT5); [| exact CE']; unfold frameE; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil|].
      split; [rewrite <- Rw' | rewrite <- Rh']; (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply OUT5; lia]). }
    assert (NA5 : numa_at C A1 M5 na h 1 arr) by (apply (numa_at_keep C A1 A1 m' M5); [exact NA' | apply sub_live_refl | exact (proj2 PM5)]).
    apply (rows NAN C A A1 m (with_vmmaps vm1 md) s ret regs S pixs w h cm data na arr CK Hs16 Hlo Hhi Hret H2 PX HOK Hw Hh Lp Ld SUB L0n L0a KX
             (Z.to_nat h) 1%Z ltac:(lia) ltac:(lia) fx' M5 r5 loc0 Hz' RS5 NA5 Hl0);
      first [exact V23 | exact V26 | (rewrite (AG5 _) by notin_list; assumption)].
Qed.

End ProfW.
