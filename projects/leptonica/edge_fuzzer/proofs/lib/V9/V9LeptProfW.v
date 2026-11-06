(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptRecs LeptArith LeptArith2 LeptScan LeptNuma LeptEdgeFP LeptRoom LeptRoom9.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptStderr V9LeptBase V9LeptUb.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9CL7a.
Import V9CL7a.V9LeptErr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9CL8a.
Import V9CL8a.V9LeptPixHdr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptCmap2 V9LeptPixCopy V9LeptEdge_iface V9LeptScan V9LeptProf.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac rok := red; apply bv_eq; reflexivity.
Ltac cs_notin Hx := unfold AllocIface.callee_saved in Hx;
  (destruct Hx as [X|[X|[X|[X|[X|X]]]]]; [discriminate X | discriminate X | discriminate X | discriminate X | discriminate X | vm_compute in X; destruct X as [X1 X2]; first [exact (X1 eq_refl) | discriminate]]).

Ltac keep_solve := let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [csr; reflexivity|]); destruct Hx.

(* [comment removed for export] *)
Local Abbreviation keepL := [3; 4; 22; 23; 24; 25; 26; 27]%bv (only parsing).

Lemma wpl1_le : forall w, (0 <= w)%Z -> (w <= 32 * wpl_of w 1)%Z.
Proof.
  intros w Hw. unfold wpl_of. rewrite Z.mul_1_r. pose proof (Z.div_mod (w + 31) 32 ltac:(lia)) as E.
  pose proof (Z.mod_pos_bound (w + 31) 32 ltac:(lia)) as R. lia.
Qed.

Section ProfW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V9Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition scan_pre (s pix : Z) (v : pixv) (m0 : word -> option byte) : Prop :=
  (0x20100 <= s)%Z /\ (s < 2 ^ 64)%Z /\ (s mod 16 = 0)%Z /\ PIXat m0 pix v /\ p_d v = 1%Z /\ (1 <= p_w v)%Z /\ (p_w v <= 32 * p_wpl v)%Z /\
  (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z /\ (p_data v mod 4 = 0)%Z /\ (4 <= p_data v)%Z /\ (4096 <= pix)%Z /\ (pix mod 8 = 0)%Z /\ (pix + 64 <= s - 240)%Z /\
  (p_data v + 4 * (p_wpl v * p_h v) <= s - 240)%Z /\
  store_ok SEGS m0 (Z_to_bv 64 (s - 240)) 240 = true /\
  (forall a : word, (p_data v <= u a < p_data v + 4 * (p_wpl v * p_h v))%Z -> m0 a <> None) /\
  rdn SEGS m0 (Z_to_bv 64 0x1c70c) 4 = Some (Z_to_le_bytes 4 0x48348) /\
  rdn SEGS m0 (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (p_w v))).

Lemma W_scan_pre : forall C A m md (s pix w h cm data : Z), Cok C -> W C A m md ->
  (c_top C - LSTK + 240 <= s)%Z -> (s <= c_top C)%Z -> (s mod 16 = 0)%Z ->
  PIXat m pix (hdv w h 1 cm data) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 1 * h))%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
  scan_pre s pix (hdv w h 1 cm data) m.
Proof.
  intros C A m md s pix w h cm data CK HW Hlo Hhi Hs16 PX HOK Hw Hh Lp Ld Rw.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w 1 ltac:(lia) DV) as Hwpl.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rd. cbn [p_data hdv] in Rd.
  assert (Rpos : (0 < 4 * (wpl_of w 1 * h))%Z) by (assert (1 * 1 <= wpl_of w 1 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Rpos) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd16 & _). rewrite u_Z2bv in ALd16 by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia.
  unfold scan_pre. cbn [p_d p_w p_h p_wpl p_data hdv].
  split; [lia|]. split; [lia|]. split; [exact Hs16|]. split; [exact PX|]. split; [reflexivity|]. split; [exact Hw|]. split; [apply wpl1_le; lia|].
  split; [change (2 ^ 26)%Z with 67108864%Z; exact Hsz|].
  split; [exact (al16_mod4 _ ALd16)|]. split; [lia|]. split; [lia|]. split; [exact (al16_mod8 _ ALp16)|]. split; [lia|]. split; [lia|].
  split; [exact (W_sok_win C A m md (s - 240) 240 CK HW ltac:(lia) ltac:(cbn; lia))|].
  split.
  { intros a Ha. destruct (blk_byte C A m md (Z_to_bv 64 data) _ a CK HW Ld ltac:(rewrite u_Z2bv by lia; exact Ha)) as (_ & D & _). exact D. }
  split; [| exact Rw].
  rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1c70c 4 HW); [rewrite p16_segs; exact jt1_val | |]; cbn [fst snd ll_ro LLU16]; lia.
Qed.

(* [comment removed for export] *)
Lemma vp_row0_b : forall (fx : FPState) s pix v m0, scan_pre s pix v m0 -> forall regs,
  (1 <= p_h v)%Z -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 1 = Z_to_bv 64 0x828e0 -> getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 (p_w v - 1) ->
  getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 (s - 68) ->
  exists regs' m' loc, msteps SEGS (mkst regs (0x82d10 : word) m0 al_rom) (mkst regs' (0x828f8 : word) m' al_rom)
    /\ sinv s m0 m' /\ (0 <= loc < p_w v)%Z /\ getr regs' 10 = Z_to_bv 64 loc
    /\ rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc))
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros fx s pix v m0 (Hs & Hs64 & Hs16 & PX0 & Hd1 & Hw1 & Hw32 & Hsz & ALd & Hdp & Gp & ALp & Hpix & Hdat & SOK0 & RDEF & JT0 & RW0) regs.
  exact (vp_row0 al_rom s pix v m0 Hs Hs64 Hs16 PX0 Hd1 Hw1 Hw32 Hsz ALd Hdp Gp ALp Hpix Hdat SOK0 RDEF JT0 RW0 regs).
Qed.

Lemma vp_row_b : forall (fx : FPState) s pix v m0, scan_pre s pix v m0 -> forall regs (loc y : Z),
  (0 <= loc < p_w v)%Z -> (0 <= y < p_h v)%Z -> rdn SEGS m0 (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc)) ->
  getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 19 = Z_to_bv 64 pix -> getr regs 20 = Z_to_bv 64 y -> getr regs 21 = Z_to_bv 64 1 ->
  exists regs' m' loc', msteps SEGS (mkst regs (0x8294c : word) m0 al_rom) (mkst regs' (0x82934 : word) m' al_rom)
    /\ sinv s m0 m' /\ (0 <= loc' < p_w v)%Z /\ getr regs' 10 = Z_to_bv 64 loc'
    /\ rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc'))
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof.
  intros fx s pix v m0 (Hs & Hs64 & Hs16 & PX0 & Hd1 & Hw1 & Hw32 & Hsz & ALd & Hdp & Gp & ALp & Hpix & Hdat & SOK0 & RDEF & JT0 & RW0) regs loc y.
  exact (vp_row al_rom s pix v m0 Hs Hs64 Hs16 PX0 Hd1 Hw1 Hw32 Hsz ALd Hdp Gp ALp Hpix Hdat SOK0 RDEF JT0 RW0 regs loc y).
Qed.

(* [comment removed for export] *)
Lemma sinv_W : forall C A m md (s : Z) m', Cok C -> W C A m md -> (c_top C - LSTK <= s - 240)%Z -> (s <= c_top C)%Z -> sinv s m m' ->
  W C A m' md /\ POSTM C A (s - 64) m m'.
Proof.
  intros C A m md s m' CK HW Hlo Hhi [G E].
  assert (OUT : forall a : word, ~ (s - 240 <= u a < s - 64)%Z -> m' a = m a) by (intros a Ha; apply E; unfold scanR; lia).
  split.
  - apply (W_local C A m md m' (s - 64) CK HW ltac:(lia)); [| exact G].
    intros a NE. left. unfold scratch. destruct (Z_lt_ge_dec (u a) (s - 240)) as [L1|G1]; [exfalso; apply NE; apply OUT; lia|].
    destruct (Z_lt_ge_dec (u a) (s - 64)) as [L2|G2]; [lia | exfalso; apply NE; apply OUT; lia].
  - apply (POSTM_range C A m md m' (s - 240) (s - 64) (s - 64) CK HW OUT); lia.
Qed.

(* [comment removed for export] *)
Lemma prof_cells_keep : forall C A m md m' (na nalloc n arr y lo hi : Z), Cok C -> W C A m md -> numa_at C A m na nalloc n arr -> (y <= nalloc)%Z ->
  LIVK A m m' -> prof_cells SEGS m arr y lo hi -> prof_cells SEGS m' arr y lo hi.
Proof.
  intros C A m md m' na nalloc n arr y lo hi CK HW NA Hy LK PC i Hi.
  pose proof NA as (Rna & ALna & Harr1 & ALarr & NEan & Hnal & Hny & Lna & _ & Larr & _).
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  destruct (NUMA_wf _ _ _ _ _ _ Rna) as (_ & _ & _ & Rarr & _).
  assert (Rpos : (0 < 4 * nalloc)%Z) by lia.
  destruct (blk_range C A m md (Z_to_bv 64 arr) _ CK HW Larr Rpos) as [Ga TOPa]. rewrite u_Z2bv in Ga, TOPa by lia.
  destruct (PC i Hi) as (v & Hv & NC). exists v. split; [exact Hv|].
  apply (ncell_livk SEGS A m m' arr (4 * nalloc) i _ NC LK Larr); lia.
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
    getr rr 10 = Z_to_bv 64 na -> numa_at C A1 mf na h h arr -> prof_cells SEGS mf arr h 0 (w - 1) ->
    realizes SEGS (mkCfg (@mkst fx' rr ret mf al_rom) md1) S.

(* [comment removed for export] *)
Definition rowst (mk : word -> option byte) : Prop :=
  W C A1 mk md1 /\ POSTM C A s m mk /\ cellsZ mk (frameP s ret regs) /\
  rdn SEGS mk (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) /\
  rdn SEGS mk (Z_to_bv 64 (s - 64)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)).

Lemma stack_facts : (c_top C - LSTK + 1376 <= s)%Z /\ (1376 <= s)%Z /\ (s < 2 ^ 64)%Z.
Proof.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  unfold GEP_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo. lia.
Qed.

Lemma rowst_scan : forall mk, rowst mk -> scan_pre s pix (hdv w h 1 cm data) mk.
Proof.
  intros mk (HWk & PMk & _ & Rw & _). destruct stack_facts as (S1 & S2 & S3).
  pose proof PX as (Hp0 & Hp64 & _).
  apply (W_scan_pre C A1 mk md1 s pix w h cm data CK HWk ltac:(lia) Hhi Hs16); [| exact HOK | exact Hw | exact Hh | exact (SUB _ _ Lp) | exact (SUB _ _ Ld) | exact Rw].
  apply (PIXat_frame m); [exact PX|]. intros x Hx. exact (LIVK_at A m mk pix 64 x (proj2 PMk) Lp ltac:(lia) ltac:(lia) Hx).
Qed.

(* [comment removed for export] *)
Lemma add_step : forall (pcF : word) (raR : Z),
  (forall (fx' : FPState) r0 m0 (loc0 na0 : Z), frm_zero (@fp_csr fx') -> (0 <= loc0 < 2 ^ 31)%Z -> getr r0 10 = Z_to_bv 64 loc0 -> getr r0 9 = Z_to_bv 64 na0 ->
     exists (fx'' : FPState) r', frm_zero (@fp_csr fx'') /\ reg_get (@fp_regs fx'') 10 = nan_box (Z_to_bv 32 (f32i loc0))
       /\ msteps SEGS (@mkst fx' r0 pcF m0 al_rom) (@mkst fx'' r' (0x61848 : word) m0 al_rom)
       /\ getr r' 1 = Z_to_bv 64 raR /\ getr r' 10 = Z_to_bv 64 na0 /\ regs_agree (fun x => In x [1; 10]%list) r0 r') ->
  ret_ok (Z_to_bv 64 raR) ->
  forall (fxk : FPState) mk r (y loc : Z), frm_zero (@fp_csr fxk) -> rowst mk -> numa_at C A1 mk na h y arr -> prof_cells SEGS mk arr y 0 (w - 1) ->
  (0 <= y < h)%Z -> (0 <= loc < w)%Z ->
  getr r 2 = Z_to_bv 64 (s - 96) -> getr r 9 = Z_to_bv 64 na -> getr r 10 = Z_to_bv 64 loc ->
  (forall (fx' : FPState) m' r', frm_zero (@fp_csr fx') -> rowst m' -> numa_at C A1 m' na h (y + 1) arr -> prof_cells SEGS m' arr (y + 1) 0 (w - 1) ->
     cs_kept r r' -> (forall a : word, (s - 96 <= u a < s)%Z -> m' a = mk a) ->
     realizes SEGS (mkCfg (@mkst fx' r' (Z_to_bv 64 raR) m' al_rom) md1) S) ->
  realizes SEGS (mkCfg (@mkst fxk r pcF mk al_rom) md1) S.
Proof using All.
  intros pcF raR SEG ROK fxk mk r y loc Hz (HWk & PMk & CEk & Rwk & Rhk) NAk PCk Hy Hl Q2 Q9 Q10 K.
  destruct stack_facts as (S1 & S2 & S3). pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  pose proof HOK as (_ & Hw2 & Hh2 & _).
  destruct (SEG fxk r mk loc na Hz ltac:(lia) Q10 Q9) as (fx1 & r1 & Hz1 & FA0 & RUN1 & E1 & E10 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |]. clear RUN1.
  replace (0x61848 : word) with (Z_to_bv 64 PC_numaAddNumber) by (apply bv_eq; reflexivity).
  apply (NAN fx1 C A A1 mk md1 r1 (s - 96)%Z na h y arr (Z_to_bv 64 raR) S Hz1 CK HWk SUB ltac:(rewrite (AG1 2%bv) by notin_list; exact Q2)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)
           E1 ROK E10 NAk ltac:(lia) L0n L0a).
  intros fx' m' r' Hz' HW' CS' PM' NA' NC' FRAME _.
  pose proof NAk as (Rna & ALna & Harr1 & ALarr & NEan & Hnal & Hny & Lna & _ & Larr & _).
  destruct (NUMA_wf _ _ _ _ _ _ Rna) as (_ & _ & _ & Rarr & Hna0 & Hna32).
  assert (Rarrpos : (0 < 4 * h)%Z) by lia.
  destruct (blk_range C A1 mk md1 (Z_to_bv 64 arr) _ CK HWk Larr Rarrpos) as [Ga TOPa]. rewrite u_Z2bv in Ga, TOPa by lia.
  destruct (blk_range C A1 mk md1 (Z_to_bv 64 na) 32 CK HWk Lna ltac:(lia)) as [Gn TOPn]. rewrite u_Z2bv in Gn, TOPn by lia.
  pose proof (ai_live_disjoint A1 mk (m_vmmaps md1) _ _ _ _ (w_inv _ _ _ _ HWk) Lna Larr ltac:(apply zneq_w; lia)) as DJ.
  rewrite !u_Z2bv in DJ by lia. pose proof (round16_ge 32 ltac:(lia)) as R32. pose proof (round16_ge (4 * h) ltac:(lia)) as R4h.
  apply (K fx' m' r' Hz'); [| exact NA' | | |].
  - split; [exact HW'|]. split; [eapply POSTM_trans; [exact PMk | eapply POSTM_mono; [| exact PM']; lia]|].
    split; [apply (cellsZ_frm C (s - 96) mk m' _ CK (proj1 PM')); [lia | | exact CEk];
            unfold frameP; repeat (apply Forall_cons; [cbn [fst]; lia|]); apply Forall_nil|].
    split; [rewrite (FRM_rdn16 C (s - 96) mk m' (s - 60) 4 CK (proj1 PM')) by (cbn; lia); exact Rwk
           | rewrite (FRM_rdn16 C (s - 96) mk m' (s - 64) 4 CK (proj1 PM')) by (cbn; lia); exact Rhk].
  - (* [comment removed for export] *)
    intros i Hi. destruct (Z.eq_dec i y) as [->|Ni].
    + exists loc. split; [lia|]. rewrite FA0, fpv_low32_box in NC'.
      destruct (ngi_table loc ltac:(lia)) as (Rf & _). rewrite fp_u_Z2bv32 in NC' by exact Rf. exact NC'.
    + destruct (PCk i ltac:(lia)) as (vi & Hvi & NCi). exists vi. split; [exact Hvi|]. unfold ncell in *. rewrite <- NCi.
      apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros a Ha. cbn in Ha. apply FRAME; unfold NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia.
  - intros x Hx. rewrite (CS' x Hx). apply AG1. cbn [In]. intros [E|[E|[]]]; subst x; cs_notin Hx.
  - intros a Ha. destruct (win_facts C a CK ltac:(unfold win; lia)) as (_ & Ga' & _).
    apply FRAME; unfold NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK; lia.
Qed.

(* [comment removed for export] *)
Definition rinv (y : Z) : Prop :=
  forall (fxk : FPState) mk r (loc : Z), frm_zero (@fp_csr fxk) -> rowst mk -> numa_at C A1 mk na h y arr -> prof_cells SEGS mk arr y 0 (w - 1) ->
    (0 <= loc < w)%Z -> rdn SEGS mk (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc)) ->
    getr r 2 = Z_to_bv 64 (s - 96) -> getr r 8 = Z_to_bv 64 0 -> getr r 9 = Z_to_bv 64 na -> getr r 19 = Z_to_bv 64 pix ->
    getr r 20 = Z_to_bv 64 y -> getr r 21 = Z_to_bv 64 1 -> (forall x, In x keepL -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (@mkst fxk r (0x8294c : word) mk al_rom) md1) S.

Lemma exit_W : forall (fxk : FPState) mk r, frm_zero (@fp_csr fxk) -> rowst mk -> numa_at C A1 mk na h h arr -> prof_cells SEGS mk arr h 0 (w - 1) ->
  getr r 2 = Z_to_bv 64 (s - 96) -> getr r 8 = Z_to_bv 64 0 -> getr r 9 = Z_to_bv 64 na -> (forall x, In x keepL -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (@mkst fxk r (0x82c2c : word) mk al_rom) md1) S.
Proof using All.
  intros fxk mk r Hz (HWk & PMk & CEk & _ & _) NAk PCk Q2 Q8 Q9 QR. destruct stack_facts as (S1 & S2 & S3).
  destruct (@vp_Z fxk al_rom r regs mk s na ret ltac:(lia) S3 Hret CEk Q2 Q8 Q9) as (r1 & RUN1 & V2 & V10 & VR & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |].
  apply (KX fxk mk r1 Hz HWk); [| exact PMk | exact V10 | exact NAk | exact PCk].
  apply cs_kept_intro; first [solve [apply VR; in_lit] | (rewrite V2, H2; reflexivity)
                            | (rewrite (AG1 _) by notin_list; apply QR; in_lit)].
Qed.

Lemma row_W : forall y, (1 <= y < h)%Z -> (y + 1 < h -> rinv (y + 1))%Z -> rinv y.
Proof.
  intros y Hy NXT. unfold rinv. intros fxk mk r loc Hz RS NAk PCk Hl Rl Q2 Q8 Q9 Q19 Q20 Q21 QR.
  destruct stack_facts as (S1 & S2 & S3). pose proof CK as [T1 T2 T3 T4 T5]. laypins.
  pose proof HOK as (_ & _ & Hh2 & _).
  pose proof RS as (HWk & PMk & CEk & Rwk & Rhk).
  destruct (@vp_row_b fxk s pix (hdv w h 1 cm data) mk (rowst_scan mk RS) r loc y Hl ltac:(cbn [p_h hdv]; lia) Rl Q2 Q19 Q20 Q21)
    as (r1 & m1 & loc' & RUN1 & SI1 & Hl' & V10 & Rl' & AG1). cbn [p_w hdv] in Hl'.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWk)) | exact (mp_lazy _ (w_pure _ _ _ _ HWk)) | exact RUN1 |]. clear RUN1.
  destruct (sinv_W C A1 mk md1 s m1 CK HWk ltac:(lia) Hhi SI1) as [HW1 PM1]. pose proof SI1 as [G1 E1].
  assert (RS1 : rowst m1).
  { split; [exact HW1|]. split; [eapply POSTM_trans; [exact PMk | apply (POSTM_sub C A A1 _ _ _ SUB); eapply POSTM_mono; [| exact PM1]; lia]|].
    split; [apply (cellsZ_keep mk m1); [| exact CEk]; unfold frameP;
            repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros z Hz0; apply E1; unfold scanR; lia]] |]); apply Forall_nil|].
    split; [rewrite <- Rwk | rewrite <- Rhk]; (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply E1; unfold scanR; lia]). }
  assert (NA1 : numa_at C A1 m1 na h y arr) by (apply (numa_at_keep C A1 A1 mk m1); [exact NAk | apply sub_live_refl | exact (proj2 PM1)]).
  assert (PC1 : prof_cells SEGS m1 arr y 0 (w - 1)) by (apply (prof_cells_keep C A1 mk md1 m1 na h y arr y 0 (w - 1) CK HWk NAk ltac:(lia) (proj2 PM1) PCk)).
  apply (add_step (0x82934 : word) 0x82940 (fun fx' r0 m0 loc0 na0 => @vp_Ck al_rom fx' r0 m0 loc0 na0) ltac:(rok) fxk m1 r1 y loc' Hz RS1 NA1 PC1 ltac:(lia) Hl').
  { rewrite (AG1 2%bv) by notin_list. exact Q2. }
  { rewrite (AG1 9%bv) by notin_list. exact Q9. }
  { exact V10. }
  intros fx' m' r' Hz' RS' NA' PC' CS' FR'.
  replace (Z_to_bv 64 0x82940) with (0x82940 : word) by (apply bv_eq; reflexivity).
  pose proof RS' as (HW' & _ & _ & _ & Rh').
  destruct (@vp_F fx' al_rom r' m' s h y _ ltac:(lia) S3 Hy ltac:(lia) eq_refl Rh') as (r2 & RUN2 & W20 & AG2).
  { rewrite (cs_kept_get _ _ _ CS' cs2), (AG1 2%bv) by notin_list. exact Q2. }
  { rewrite (cs_kept_get _ _ _ CS' cs20), (AG1 20%bv) by notin_list. exact Q20. }
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN2 |]. clear RUN2.
  assert (R2 : getr r2 2 = Z_to_bv 64 (s - 96)) by (rewrite (AG2 2%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs2), (AG1 2%bv) by notin_list; exact Q2).
  assert (R8 : getr r2 8 = Z_to_bv 64 0) by (rewrite (AG2 8%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs8), (AG1 8%bv) by notin_list; exact Q8).
  assert (R9 : getr r2 9 = Z_to_bv 64 na) by (rewrite (AG2 9%bv) by notin_list; rewrite (cs_kept_get _ _ _ CS' cs9), (AG1 9%bv) by notin_list; exact Q9).
  assert (RR : forall x, In x keepL -> getr r2 x = getr regs x) by keep_solve.
  assert (Rl2 : rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc'))).
  { rewrite <- Rl'. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply FR'; lia]. }
  destruct (Z.ltb_spec (y + 1) h) as [LT|GE].
  - apply (NXT LT fx' m' r2 loc' Hz' RS' NA' PC' Hl' Rl2 R2 R8 R9); [| exact W20 | | exact RR].
    + rewrite (AG2 19%bv) by notin_list. rewrite (cs_kept_get _ _ _ CS' cs19), (AG1 19%bv) by notin_list. exact Q19.
    + rewrite (AG2 21%bv) by notin_list. rewrite (cs_kept_get _ _ _ CS' cs21), (AG1 21%bv) by notin_list. exact Q21.
  - replace (y + 1)%Z with h in NA', PC' by lia.
    exact (exit_W fx' m' r2 Hz' RS' NA' PC' R2 R8 R9 RR).
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
  replace (Z_to_bv 64 PC_pixGetEdgeProfile) with (0x82768 : word) by (apply bv_eq; reflexivity).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (SF : (c_top C - LSTK + 1376 <= s)%Z) by (unfold GEP_STACK, NAN_STACK, NEX_STACK, RNW_STACK, CALLOC_STACK, ALLOC_STACK in Hlo; lia).
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia.
  (* [comment removed for export] *)
  destruct (@vp_A fx al_rom regs m s pixs (hdv w h 1 cm data) ret ltac:(lia) ltac:(lia) Hs16 PX eq_refl Gp (al16_mod8 _ ALp16) ltac:(lia)
              (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q8 & Q18 & Q19 & Q20 & AG1). cbn [p_w p_h hdv] in RUN1, Q10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |]. clear RUN1.
  set (M1 := DIMS (FRP m s ret regs) (s - 60) (s - 64) w h).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold DIMS, FRP; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (CE1 : cellsZ M1 (frameP s ret regs)) by (subst M1; unfold DIMS, FRP, frameP; cbn [cellsZ]; repeat split; rdn_solve).
  assert (Rw1 : rdn SEGS M1 (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))).
  { subst M1. unfold DIMS. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (Rh1 : rdn SEGS M1 (Z_to_bv 64 (s - 64)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { subst M1. unfold DIMS. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  (* [comment removed for export] *)
  replace (0x61688 : word) with (Z_to_bv 64 PC_numaCreate) by (apply bv_eq; reflexivity).
  assert (En0 : numa_n0 h = h) by (unfold numa_n0; destruct (Z.leb_spec 1 h), (Z.leb_spec h 100000000); cbn; lia).
  apply (NCR fx C A M1 md r1 (s - 96)%Z h (Z_to_bv 64 0x82878) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold NCR_STACK, CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia) Q1 ltac:(rok) ltac:(rewrite (AG1 4%bv) by notin_list; exact H4) Q10 ltac:(lia)
           kR bR Hrm Hrk ltac:(rewrite En0; exact Hrb)).
  rewrite En0.
  intros A1 m2 vm1 r2 na arr HW2 CS2 PM2 A10 (NA2 & L0n & L0a & LEQ) Hrm1.
  replace (Z_to_bv 64 0x82878) with (0x82878 : word) by (apply bv_eq; reflexivity).
  assert (SUB : sub_live A A1) by (intros q k Lq; rewrite LEQ; [exact Lq | intros E; subst q; congruence | intros E; subst q; congruence]).
  assert (PMa : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [| exact PM2]; lia]).
  assert (CE2 : cellsZ m2 (frameP s ret regs)).
  { apply (cellsZ_frm C (s - 96) M1 m2 _ CK (proj1 PM2)); [lia | | exact CE1]. unfold frameP. repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. }
  assert (Rw2 : rdn SEGS m2 (Z_to_bv 64 (s - 60)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))) by (rewrite (FRM_rdn16 C (s - 96) M1 m2 (s - 60) 4 CK (proj1 PM2)) by (cbn; lia); exact Rw1).
  assert (Rh2 : rdn SEGS m2 (Z_to_bv 64 (s - 64)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (rewrite (FRM_rdn16 C (s - 96) M1 m2 (s - 64) 4 CK (proj1 PM2)) by (cbn; lia); exact Rh1).
  assert (RS2 : rowst C A A1 m (with_vmmaps vm1 md) s ret regs w h m2) by (split; [exact HW2|]; split; [exact PMa|]; split; [exact CE2|]; split; [exact Rw2 | exact Rh2]).
  (* [comment removed for export] *)
  assert (KX : forall (fx' : FPState) mf rr, frm_zero (@fp_csr fx') -> W C A1 mf (with_vmmaps vm1 md) -> cs_kept regs rr -> POSTM C A s m mf ->
             getr rr 10 = Z_to_bv 64 na -> numa_at C A1 mf na h h arr -> prof_cells SEGS mf arr h 0 (w - 1) ->
             realizes SEGS (mkCfg (@mkst fx' rr ret mf al_rom) (with_vmmaps vm1 md)) S).
  { intros fx' mf rr Hz' HWf CSf PMf A10f NAf PCf. exact (HK fx' A1 mf vm1 rr na arr Hz' HWf CSf PMf A10f NAf L0n L0a LEQ PCf Hrm1). }
  (* [comment removed for export] *)
  destruct (@vp_B fx al_rom r2 m2 s pixs na w ltac:(lia) ltac:(lia) ltac:(lia) Rw2
              ltac:(rewrite (cs_kept_get _ _ _ CS2 cs2); exact Q2) A10 ltac:(rewrite (cs_kept_get _ _ _ CS2 cs18); exact Q18)
              ltac:(rewrite (cs_kept_get _ _ _ CS2 cs19); exact Q19) ltac:(rewrite (cs_kept_get _ _ _ CS2 cs20); exact Q20))
    as (r3 & RUN3 & V2 & V1 & V9 & V10 & V11 & V12 & V13 & V14 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |]. clear RUN3.
  (* [comment removed for export] *)
  destruct (@vp_row0_b fx s pixs (hdv w h 1 cm data) m2 (rowst_scan C A A1 m _ s ret regs pixs w h cm data CK Hs16 Hlo Hhi PX HOK Hw Hh Lp Ld SUB m2 RS2) r3 ltac:(cbn [p_h hdv]; lia)
              V2 V1 V10 V11 V12 V13 V14)
    as (r4 & m4 & loc0 & RUN4 & SI4 & Hl0 & W10 & Rl4 & AG4). cbn [p_w hdv] in Hl0.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |]. clear RUN4.
  destruct (sinv_W C A1 m2 _ s m4 CK HW2 ltac:(lia) Hhi SI4) as [HW4 PM4]. pose proof SI4 as [G4 E4].
  assert (RS4 : rowst C A A1 m (with_vmmaps vm1 md) s ret regs w h m4).
  { split; [exact HW4|]. split; [eapply POSTM_trans; [exact PMa | apply (POSTM_sub C A A1 _ _ _ SUB); eapply POSTM_mono; [| exact PM4]; lia]|].
    split; [apply (cellsZ_keep m2 m4); [| exact CE2]; unfold frameP;
            repeat (apply Forall_cons; [cbn [fst]; split; [lia | split; [lia | intros z Hz0; apply E4; unfold scanR; lia]] |]); apply Forall_nil|].
    split; [rewrite <- Rw2 | rewrite <- Rh2]; (apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply E4; unfold scanR; lia]). }
  assert (NA4 : numa_at C A1 m4 na h 0 arr) by (apply (numa_at_keep C A1 A1 m2 m4); [exact NA2 | apply sub_live_refl | exact (proj2 PM4)]).
  assert (PC4 : prof_cells SEGS m4 arr 0 0 (w - 1)) by (intros i Hi; lia).
  assert (E2 : getr r4 2 = Z_to_bv 64 (s - 96)) by (rewrite (AG4 2%bv) by notin_list; exact V2).
  assert (E9 : getr r4 9 = Z_to_bv 64 na) by (rewrite (AG4 9%bv) by notin_list; exact V9).
  apply (add_step NAN C A A1 m (with_vmmaps vm1 md) s ret regs S pixs w h cm data na arr CK Hs16 Hlo Hhi Hret H2 PX HOK Hw Hh Lp Ld SUB L0n L0a KX
           (0x828f8 : word) 0x82904 (fun fx' r0 m0 loc1 na0 => @vp_C0 al_rom fx' r0 m0 loc1 na0) ltac:(rok) fx m4 r4 0%Z loc0 Hfz RS4 NA4 PC4 ltac:(lia) Hl0 E2 E9 W10).
  intros fx' m' r' Hz' RS' NA' PC' CS' FR'. replace (0 + 1)%Z with 1%Z in NA', PC' by lia.
  replace (Z_to_bv 64 0x82904) with (0x82904 : word) by (apply bv_eq; reflexivity).
  pose proof RS' as (HW' & PM' & CE' & Rw' & Rh').
  assert (B2 : getr r' 2 = Z_to_bv 64 (s - 96)) by (rewrite (cs_kept_get _ _ _ CS' cs2); exact E2).
  assert (B8 : getr r' 8 = Z_to_bv 64 0).
  { rewrite (cs_kept_get _ _ _ CS' cs8). rewrite (AG4 8%bv) by notin_list. rewrite (AG3 8%bv) by notin_list. rewrite (cs_kept_get _ _ _ CS2 cs8). exact Q8. }
  assert (B9 : getr r' 9 = Z_to_bv 64 na) by (rewrite (cs_kept_get _ _ _ CS' cs9); exact E9).
  assert (B19 : getr r' 19 = Z_to_bv 64 pixs).
  { rewrite (cs_kept_get _ _ _ CS' cs19). rewrite (AG4 19%bv) by notin_list. rewrite (AG3 19%bv) by notin_list. rewrite (cs_kept_get _ _ _ CS2 cs19). exact Q19. }
  assert (BR : forall x, In x keepL -> getr r' x = getr regs x) by keep_solve.
  assert (Rl' : rdn SEGS m' (Z_to_bv 64 (s - 68)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 loc0))).
  { rewrite <- Rl4. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia | intros a Ha; cbn in Ha; apply FR'; lia]. }
  destruct (Z_lt_ge_dec h 2) as [H1'|H2'].
  - (* [comment removed for export] *)
    assert (h = 1)%Z by lia. subst h.
    destruct (@vp_D_exit fx' al_rom r' m' s ltac:(lia) ltac:(lia) Rh' B2) as (r5 & RUN5 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN5 |]. clear RUN5.
    apply (exit_W NAN C A A1 m (with_vmmaps vm1 md) s ret regs S pixs w 1%Z cm data na arr CK Hs16 Hlo Hhi Hret H2 PX HOK Hw Hh Lp Ld SUB L0n L0a KX fx' m' r5 Hz' RS' NA' PC');
      first [ (rewrite (AG5 _) by notin_list; assumption)
            | keep_solve ].
  - (* [comment removed for export] *)
    destruct (@vp_D_loop fx' al_rom r' m' s h ltac:(lia) ltac:(lia) ltac:(lia) Rh' B2) as (r5 & RUN5 & V20 & V21 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN5 |]. clear RUN5.
    apply (rows NAN C A A1 m (with_vmmaps vm1 md) s ret regs S pixs w h cm data na arr CK Hs16 Hlo Hhi Hret H2 PX HOK Hw Hh Lp Ld SUB L0n L0a KX
             (Z.to_nat h) 1%Z ltac:(lia) ltac:(lia) fx' m' r5 loc0 Hz' RS' NA' PC' Hl0 Rl');
      first [ exact V20 | exact V21 | (rewrite (AG5 _) by notin_list; assumption)
            | keep_solve ].
Qed.

End ProfW.
