(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL7a.
Import V15CL7a.V15LeptErr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL9a.
Import V15CL9a.V15LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid. Import V15CL10a.V15LeptPixCreateS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopyA V15LeptPixCopy V15LeptPixHdrS V15LeptPixDestroyK.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL14a.
Import V15CL14a.V15LeptThrLeaf. Import V15CL14a.V15LeptDither_iface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptExecT LeptArith LeptRoomPC LeptRoom14.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.

Definition THRT_WIN : Z := 4608.
Definition STOPS : list Z := [95132; 95788; 95932; 106268; 122032; 166484; 94372]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_PIXCREATE : word := 93000%bv.
Lemma PC_PIXCREATE_eq : Z_to_bv 64 93000 = PC_PIXCREATE. Proof. apply bv_eq; reflexivity. Qed.
Definition PC_SETCMAP : word := 95932%bv.
Lemma PC_SETCMAP_eq : Z_to_bv 64 95932 = PC_SETCMAP. Proof. apply bv_eq; reflexivity. Qed.
Definition PC_DESTROY : word := 94372%bv.
Lemma PC_DESTROY_eq : Z_to_bv 64 94372 = PC_DESTROY. Proof. apply bv_eq; reflexivity. Qed.
Definition ex_rg1 : reg := 1%bv. Definition ex_rg8 : reg := 8%bv. Definition ex_rg9 : reg := 9%bv. Definition ex_rg18 : reg := 18%bv. Definition ex_rg19 : reg := 19%bv. Definition ex_rg20 : reg := 20%bv. Definition ex_rg21 : reg := 21%bv. Definition ex_rg22 : reg := 22%bv. Definition ex_rg23 : reg := 23%bv. Definition ex_rg24 : reg := 24%bv. Definition ex_rg25 : reg := 25%bv. Definition ex_rg26 : reg := 26%bv. Definition ex_rg27 : reg := 27%bv. 
Definition ex_r14 : reg := 14%bv. Definition ex_r18 : reg := 18%bv. Definition ex_r19 : reg := 19%bv.
Definition LUT_HEAD : Z := 122032.   Definition LUT_EXIT : Z := 122360.
Definition LUT_CLOB : list reg := [5; 6; 7; 8; 10; 11; 12; 13; 15; 16; 17; 20; 22; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Definition thr_lut_hop : Prop := forall (fx : FPState) C A Ar M md regs (s w h datad datat qtab : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (c_top C - LSTK + THRT_WIN <= s)%Z -> (s <= c_top C)%Z ->
  hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 8 * h))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datat) = Some (4 * (wpl_of w 8 * h))%Z -> live A (Z_to_bv 64 qtab) = Some 1024%Z ->
  Z_to_bv 64 datad <> Z_to_bv 64 qtab -> (0 <= datad < 2 ^ 64)%Z -> (0 <= datat < 2 ^ 64)%Z -> (0 <= qtab < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -208) -> getr regs 11 = Z_to_bv 64 h ->
  getr regs 18 = Z_to_bv 64 datad -> getr regs 9 = Z_to_bv 64 datat -> getr regs 19 = Z_to_bv 64 (wpl_of w 8) -> getr regs 14 = Z_to_bv 64 (wpl_of w 8) ->
  rdn SEGS M (Z_to_bv 64 (s + -128)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS M (Z_to_bv 64 (s + -124)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS M (Z_to_bv 64 (s + -120)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' -> regs_agree (fun r => In r LUT_CLOB) regs regs' ->
      (forall x : word, ~ (datad <= u x < datad + 4 * (wpl_of w 8 * h))%Z -> m' x = M x) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 LUT_EXIT) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 LUT_HEAD) M al_rom) md) S.

Lemma cmf_keep : forall (fx : FPState) (A A' : AS) (m m' : word -> option byte) (cm : Z) (cv : cmapv), cm_facts A m cm cv -> sub_live A A' -> LIVK A m m' -> cm_facts A' m' cm cv.
Proof.
  intros fx A A' m m' cm cv [->|(CM & OK & L1 & L2)] SUB LK; [left; reflexivity | right].
  split; [exact (exT_cmap_livk A m m' cm cv CM LK L1) | split; [exact OK | split; [exact (SUB _ _ L1) | exact (SUB _ _ L2)]]].
Qed.
Lemma fresh_sub : forall (Ar A : AS) (q : word), sub_live Ar A -> live A q = None -> live Ar q = None.
Proof. intros Ar A q SUB F. destruct (live Ar q) as [k|] eqn:EE; [|reflexivity]. rewrite (SUB _ _ EE) in F. discriminate F. Qed.
Lemma ne_live : forall (A : AS) (p q : word) (k : Z), live A p = Some k -> live A q = None -> p <> q.
Proof. intros A p q k L F ->. rewrite F in L. discriminate L. Qed.

Section Tail.
Hypothesis HRMC : pixRemoveColormap_gray8_contract.
Hypothesis HRC2 : pixDestroy_rc2_contract.
Hypothesis HLUT : thr_lut_hop.

Lemma thr_tail_W : forall (fx : FPState) C Ar A m md regs (regsE : bvmap 5 word) (s pixs w h cm data qtab cmap cmaparr : Z) (cv : cmapv) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md -> sub_live Ar A ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + THRT_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = Z_to_bv 64 121728 -> getr regs 2 = Z_to_bv 64 (s + -208) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 284096 ->
  getr regs 8 = Z_to_bv 64 8 -> getr regs 9 = Z_to_bv 64 pixs -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 8 ->
  rdn SEGS m (Z_to_bv 64 (s + -8)) 8 = Some (word_to_le_bytes 8 (getr regsE 1)) ->
  rdn SEGS m (Z_to_bv 64 (s + -16)) 8 = Some (word_to_le_bytes 8 (getr regsE 8)) ->
  rdn SEGS m (Z_to_bv 64 (s + -24)) 8 = Some (word_to_le_bytes 8 (getr regsE 9)) ->
  rdn SEGS m (Z_to_bv 64 (s + -32)) 8 = Some (word_to_le_bytes 8 (getr regsE 18)) ->
  rdn SEGS m (Z_to_bv 64 (s + -40)) 8 = Some (word_to_le_bytes 8 (getr regsE 19)) ->
  rdn SEGS m (Z_to_bv 64 (s + -48)) 8 = Some (word_to_le_bytes 8 (getr regsE 20)) ->
  rdn SEGS m (Z_to_bv 64 (s + -56)) 8 = Some (word_to_le_bytes 8 (getr regsE 21)) ->
  rdn SEGS m (Z_to_bv 64 (s + -64)) 8 = Some (word_to_le_bytes 8 (getr regsE 22)) ->
  rdn SEGS m (Z_to_bv 64 (s + -72)) 8 = Some (word_to_le_bytes 8 (getr regsE 23)) ->
  rdn SEGS m (Z_to_bv 64 (s + -80)) 8 = Some (word_to_le_bytes 8 (getr regsE 24)) ->
  rdn SEGS m (Z_to_bv 64 (s + -88)) 8 = Some (word_to_le_bytes 8 (getr regsE 25)) ->
  rdn SEGS m (Z_to_bv 64 (s + -96)) 8 = Some (word_to_le_bytes 8 (getr regsE 26)) ->
  rdn SEGS m (Z_to_bv 64 (s + -104)) 8 = Some (word_to_le_bytes 8 (getr regsE 27)) ->
  rdn SEGS m (Z_to_bv 64 (s + -160)) 8 = Some (Z_to_le_bytes 8 cmap) ->
  rdn SEGS m (Z_to_bv 64 (s + -128)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s + -124)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s + -120)) 8 = Some (Z_to_le_bytes 8 qtab) ->
  getr regsE 1 = ret -> ret_ok ret -> getr regsE 2 = Z_to_bv 64 s -> getr regsE 4 = Z_to_bv 64 284096 ->
  PIXat m pixs (hdv w h 8 cm data) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z -> cm_facts A m cm cv ->
  live A (Z_to_bv 64 qtab) = Some 1024%Z -> live Ar (Z_to_bv 64 qtab) = None -> live (c_A0 C) (Z_to_bv 64 qtab) = None -> (0 <= qtab < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 cmap) = Some 24%Z -> live Ar (Z_to_bv 64 cmap) = None -> live (c_A0 C) (Z_to_bv 64 cmap) = None ->
  live A (Z_to_bv 64 cmaparr) = Some 1024%Z -> live Ar (Z_to_bv 64 cmaparr) = None -> live (c_A0 C) (Z_to_bv 64 cmaparr) = None ->
  CMAPat m cmap (CMAPV cmaparr 8 256 5 0) -> Z_to_bv 64 cmaparr <> Z_to_bv 64 qtab ->
  (forall q : word, ~ In q [Z_to_bv 64 qtab; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A q = live Ar q) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix + RK_rmc <= kR)%Z -> (RB_pix14 + RB_rmc <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regsE regs' -> POSTM C Ar s m m' ->
      (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C Ar A' m' pixd w h 8 cmap datad (CMAPV cmaparr 8 256 5 0)) ->
      aroom A' vm' (kR - RK_pix - RK_rmc) (bR - RB_pix14 - RB_rmc) ->
      realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 93000) m al_rom) md) S.
Proof.
  intros fx C Ar A0 m0 md r0 regsE s pixs w h cm data qtab cmap cmaparr cv ret S FZ CK HW0 SUBr Hs16 Hlo Hhi H1 H2 H3 H4 H8 H9 H10 H11 H12
         SV1 SV8 SV9 SV18 SV19 SV20 SV21 SV22 SV23 SV24 SV25 SV26 SV27 LCcmap LCh LCw LCqtab HE1 Hret HE2 HE4
         PXs HOK Hw1 Hh1 Lpixs_a0 F0pixs Ldata_a0 CMF Lqtab_a0 Fqtab F0qtab RRqtab Lcmap_a0 Fcmap F0cmap Lcmaparr_a0 Fcmaparr F0cmaparr CMP NE_cmaparr_qtab LDEL0 kR bR RM0 HkR HbR HC.
  unfold THRT_WIN in *.
  assert (HRA : ex_keep (Z_to_bv 64 (bv_unsigned (getr regsE ex_rg1)) = ret)) by (unfold ex_keep; rewrite zbv_self; exact HE1).
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  assert (HE2k : ex_keep (getr regsE ex_r2 = Z_to_bv 64 s)) by exact HE2.
  assert (HE4k : ex_keep (getr regsE ex_r4 = Z_to_bv 64 284096)) by exact HE4.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 4608)%Z) by lia.
  assert (GLO2 : (s - 4608 + Z.of_nat (Z.to_nat 4608) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (4608 <= s)%Z) by lia.
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rwpl : (1 <= wpl_of w 8 < 2 ^ 31)%Z).
  { destruct HOK as (_ & _ & _ & X). assert (1 <= wpl_of w 8)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  assert (Rn1 : (0 < 4 * (wpl_of w 8 * h))%Z) by nia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  pose proof PXs as (Hps0 & Hps64 & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof CMP as (Hcm0 & Hcm24 & _). assert (RRcmap : (0 <= cmap < 2 ^ 64)%Z) by lia.
  assert (Lpixs_r : live Ar (Z_to_bv 64 pixs) = Some 64%Z).
  { rewrite <- (LDEL0 (Z_to_bv 64 pixs)); [exact Lpixs_a0|]. intros [EE|[EE|[EE|[]]]]; rewrite <- EE in Lpixs_a0;
      [rewrite Lqtab_a0 in Lpixs_a0 | rewrite Lcmaparr_a0 in Lpixs_a0 | rewrite Lcmap_a0 in Lpixs_a0]; discriminate Lpixs_a0. }
  destruct (exT_blk_top32 C A0 m0 _ cmap CK HW0 Lcmap_a0 RRcmap) as [Gcm1 Gcm2].
  assert (RRcmaparr : (0 <= cmaparr < 2 ^ 64)%Z) by (destruct CMP as (_ & _ & WFc & _); exact (cf_arr _ WFc)).
  destruct (exW_blk_rng C A0 m0 _ cmaparr 1024 CK HW0 Lcmaparr_a0 RRcmaparr ltac:(lia)) as (Gca1 & Gca2 & _).
  assert (CMOK : cmap_ok (CMAPV cmaparr 8 256 5 0)).
  { unfold cmap_ok. cbn. split; [right; right; right; reflexivity|]. split; [reflexivity|]. split; lia. }
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); qtab; cmap; cmaparr; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 434688 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KWord (SA (EVar 32) (-8)) 8 (EVar 37); KWord (SA (EVar 32) (-16)) 8 (EVar 38); KWord (SA (EVar 32) (-24)) 8 (EVar 39); KWord (SA (EVar 32) (-32)) 8 (EVar 40); KWord (SA (EVar 32) (-40)) 8 (EVar 41); KWord (SA (EVar 32) (-48)) 8 (EVar 42); KWord (SA (EVar 32) (-56)) 8 (EVar 43); KWord (SA (EVar 32) (-64)) 8 (EVar 44); KWord (SA (EVar 32) (-72)) 8 (EVar 45); KWord (SA (EVar 32) (-80)) 8 (EVar 46); KWord (SA (EVar 32) (-88)) 8 (EVar 47); KWord (SA (EVar 32) (-96)) 8 (EVar 48); KWord (SA (EVar 32) (-104)) 8 (EVar 49); KWord (SA (EVar 32) (-160)) 8 (EVar 51); KWord (SA (EVar 32) (-128)) 4 (EVar 36); KWord (SA (EVar 32) (-124)) 4 (EVar 35); KWord (SA (EVar 32) (-120)) 8 (EVar 50)]).
  { repeat (apply Forall_cons || apply Forall_nil).
    - ex_know1 r0.
    - ex_know1 r0.
    - ex_know1 r0.
    - ex_know1 r0.
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV18].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV19].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV20].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV21].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV22].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV23].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV24].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV25].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV26].
    - eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV27].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCcmap].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCh].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCw].
    - eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact LCqtab].
  }
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 4608) (Z.to_nat 4608) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); qtab; cmap; cmaparr; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); qtab; cmap; cmaparr; exW_canary SEGS 415784 m0]) (EVar 53) (EVar 32) (exW_canary SEGS 415784 m0) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 HKf0)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); qtab; cmap; cmaparr; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 4608 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  rewrite PC_PIXCREATE_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCreate_sure_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) w h 8 (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0 Q12_0 Hw1 Hh1 HOK kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) ltac:(clear - HkR; unfold RK_rmc, RK_pix in *; lia) ltac:(clear - HbR; unfold RB_rmc, RB_pix14 in *; lia)) end end.
  intros A1 m1 vm1 r1 pixd datad HW1 CSx0 PMc0 A10_0 PXN RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixdx & Fdatadx & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ0 & PXd1 & _).
  change (p_wpl (set_data (pix_hdr w h 8) datad)) with (wpl_of w 8) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 8) datad)) with h in Gdd2, Ldatad_a1.
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdatad : (0 <= datad < 2 ^ 64)%Z) by lia.
  assert (SUB1 : sub_live A0 A1).
  { intros q0 kq Lq. rewrite (LEQ0 q0 (ne_live A0 q0 _ kq Lq Fpixdx) (ne_live A0 q0 _ kq Lq Fdatadx)). exact Lq. }
  pose proof (SUB1 _ _ Lpixs_a0) as Lpixs_a1. pose proof (SUB1 _ _ Ldata_a0) as Ldata_a1. pose proof (SUB1 _ _ Lqtab_a0) as Lqtab_a1.
  pose proof (SUB1 _ _ Lcmap_a0) as Lcmap_a1. pose proof (SUB1 _ _ Lcmaparr_a0) as Lcmaparr_a1.
  pose proof (fresh_sub Ar A0 _ SUBr Fpixdx) as Fpixd. pose proof (fresh_sub Ar A0 _ SUBr Fdatadx) as Fdatad.
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fpixdx) as NE_pixs_pixd.
  assert (NE_pixd_cmap : Z_to_bv 64 pixd <> Z_to_bv 64 cmap) by (intros EE; exact (ne_live A0 _ _ _ Lcmap_a0 Fpixdx (eq_sym EE))).
  assert (LDEL1 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad; Z_to_bv 64 qtab; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A1 q0 = live Ar q0).
  { intros q0 Hq. rewrite (LEQ0 q0 (fun EE => Hq (or_introl (eq_sym EE))) (fun EE => Hq (or_intror (or_introl (eq_sym EE))))). apply LDEL0. intros XX. apply Hq. right; right; exact XX. }
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 4608 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 54%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 8; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixd; datad; wpl_of w 8; exW_canary SEGS 415784 m1] 54%nat ltac:(vm_cast_no_check (eq_refl 54%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixd; datad; wpl_of w 8; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 54%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 54%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 8; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 86) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 LEQ0 RM0 LDEL0 A10_0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_pix SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 8; exW_canary SEGS 415784 m1]) (EVar 86) (EVar 32) (EVar 87) (EVar 88) pixd s 4608 _ CK HW1 Lpixd_a1 PXd1 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 4608) (Z.to_nat 4608) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 8; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 8; exW_canary SEGS 415784 m1]) (EVar 89) (EVar 32) (exW_canary SEGS 415784 m1) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 4608 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (PXsM1 : PIXat M1 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M1 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM1 PMs1)) Lpixs_a0).
  assert (PXdM1 : PIXat M1 pixd (set_data (pix_hdr w h 8) datad)) by exact (exT_pix_sess C A1 m1 M1 _ s 4608 pixd _ CK HW1 GLO1 Lpixd_a1 PXd1 FRs1).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyRes0_W fxk C A0 A1 M1 _ Rc1 (s + OFF1) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs1 SUB1 Q2_1
             ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q10_1 Q11_1 PXsM1 PXdM1 eq_refl eq_refl eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixdx F0pixd NE_pixs_pixd) end end.
  intros m2 r2 HW2 CSx1 PMc1 PXd2 A10_1.
  pose proof CSx1 as CS1. clear CSx1.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_mono C A0 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 4608 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 90%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 415784 m2] 90%nat ltac:(vm_cast_no_check (eq_refl 90%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 90%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 90%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 A10_1 PXsM1 PXdM1 PXd1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m2 _ (s - 4608) (Z.to_nat 4608) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) (EVar 122) (EVar 32) (exW_canary SEGS 415784 m2) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A1 A0 m2 _ E2 log2 (EVar 32) s 4608 [] CK HW2 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M2 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM2 PMs2)) Lpixs_a0).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 8) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 4608 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyFmt0_W fxk C A0 A1 M2 _ Rc2 (s + OFF2) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs2 SUB1 Q2_2
             ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) Q1_2 ltac:(red; apply bv_eq; reflexivity) Q10_2 Q11_2 PXsM2 PXdM2 eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixdx F0pixd NE_pixs_pixd) end end.
  intros m3 r3 HW3 CSx2 PMc2 PXd3 A10_2.
  pose proof CSx2 as CS2. clear CSx2.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_mono C A0 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 4608 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 123%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 123%nat ltac:(vm_cast_no_check (eq_refl 123%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 123%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 123%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 PM2 HW2 FRs2 PMc2 CS2 OFF2 A10_2 PXsM2 PXdM2 PXd2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m3 _ (s - 4608) (Z.to_nat 4608) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 155) (EVar 32) (exW_canary SEGS 415784 m3) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A1 A0 m3 _ E3 log3 (EVar 32) s 4608 [] CK HW3 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  assert (PXdM3 : PIXat M3 pixd (set_data (pix_hdr w h 8) datad)) by exact (exT_pix_sess C A1 m3 M3 _ s 4608 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3).
  assert (CMPM3 : CMAPat M3 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_livk A0 m0 M3 cmap _ CMP (proj2 (POSTM_trans _ _ _ _ _ _ PM3 PMs3)) Lcmap_a0).
  rewrite PC_SETCMAP_eq.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixSetColormap_W (fx := fxk) C A0 A1 M3 _ Rc3 (s + OFF3) pixd cmap (set_data (pix_hdr w h 8) datad) (CMAPV cmaparr 8 256 5 0) (Z_to_bv 64 ra) S CK HWs3 SUB1 Q2_3
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF3; lia) ltac:(unfold OFF3; lia) Q1_3 ltac:(red; apply bv_eq; reflexivity) Q10_3 Q11_3
             PXdM3 eq_refl Lpixd_a1 Fpixdx F0pixd CMPM3 CMOK Lcmap_a1 NE_pixd_cmap) end end.
  intros m4 r4 HW4 CSx3 PMc3 PXd4 CMP4 A10_3.
  pose proof CSx3 as CS3. clear CSx3.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_mono C A0 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 4608 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 156%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 156%nat ltac:(vm_cast_no_check (eq_refl 156%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 156%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 156%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 PM3 HW3 FRs3 PMc3 CS3 OFF3 A10_3 PXdM3 CMPM3 PXd3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exT_kn_cells SEGS m4 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 86) (EVar 87) (EVar 88) pixd _ PXd4 eq_refl eq_refl eq_refl) as HKg4.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m4 _ (s - 4608) (Z.to_nat 4608) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 188) (EVar 32) (exW_canary SEGS 415784 m4) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A1 A0 m4 _ E4 log4 (EVar 32) s 4608 [] CK HW4 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r1 Q1_4. exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r4 Q4_4.
  clear BS4.
  lazymatch type of Q2_4 with _ = Z_to_bv 64 (s + ?off) => pose (OFF4 := off) end.
  (* [comment removed for export] *)
  assert (PXsM4 : PIXat M4 pixs (hdv w h 8 cm data)) by exact (exT_pix_livk A0 m0 M4 pixs _ PXs (proj2 (POSTM_trans _ _ _ _ _ _ PM4 PMs4)) Lpixs_a0).
  assert (PXdM4 : PIXat M4 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_sess C A1 m4 M4 _ s 4608 pixd _ CK HW4 GLO1 Lpixd_a1 PXd4 FRs4).
  assert (CMPM4 : CMAPat M4 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_sess C A1 m4 M4 _ s 4608 cmap _ CK HW4 GLO1 Lcmap_a1 CMP4 FRs4).
  assert (CMF4 : cm_facts A1 M4 cm cv) by exact (cmf_keep _ A0 A1 m0 M4 cm cv CMF SUB1 (proj2 (POSTM_trans _ _ _ _ _ _ PM4 PMs4))).
  assert (PMB : POSTM C Ar s m0 M4) by exact (POSTM_sub C Ar A0 _ _ _ SUBr (POSTM_trans _ _ _ _ _ _ PM4 PMs4)).
  pose proof (sub_live_trans _ _ _ SUBr SUB1) as SUBr1.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HRMC fxk C A1 M4 _ Rc4 (s + OFF4)%Z pixs w h cm data cv (Z_to_bv 64 ra) S FZ CK HWs4 Q2_4
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF4, RMC_STACK, LSF; lia) ltac:(unfold OFF4; lia) Q1_4 ltac:(red; apply bv_eq; reflexivity) Q4_4 Q10_4 Q11_4
             PXsM4 HOK Hw1 Hh1 Lpixs_a1 F0pixs Ldata_a1 CMF4 (kR - RK_pix)%Z (bR - RB_pix14)%Z
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR; lia) ltac:(clear - HbR; lia)) end end.
  intros fx2 A2 m5 vm2 r5 FZ2 HW5 CSx4 OUT RM2.
  destruct fx2 as [fr2 cs2]. cbn [fp_csr] in FZ2. clear FZ. rename FZ2 into FZ.
  pose proof CSx4 as CS4. clear CSx4.
  rewrite with_vmmaps_twice in HW5 |- *.
  destruct OUT as [(Ecm & A10_4 & LEQ4 & PMc4) | (NEcm & PMc4 & pixt & datat & A10_4 & PTN)].
  - (* [comment removed for export] *)
    subst cm.
    assert (PMR : POSTM C A1 s (wbytes M4 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m5) by (apply (POSTM_mono C A1 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]).
    assert (CLONEK : forall (Ax : AS) (mx my : word -> option byte) (mdx : Model) (pp : Z), W C Ax mx mdx -> sub_live Ar Ax -> (0 <= pp)%Z -> (c_top C - LSTK <= pp)%Z -> (pp + 8 <= s)%Z ->
               POSTM C Ar s m5 mx -> POSTM C Ax (pp + 8) (wbytes (wbytes mx (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) my -> POSTM C Ar s m0 my).
    { intros Ax mx my mdx pp HWx SUBx P0 P1 P2 PM23 PM34. eapply POSTM_trans; [exact PMB|].
      exact (exT_postm_clone C Ar A1 Ax M4 m5 mx my _ mdx s pp pixs (hdv w h 8 0 data) CK HWs4 HWx SUBr1 SUBx PXsM4 eq_refl Lpixs_r P0 P1 P2 Hhi PMR PM23 PM34). }
    assert (PXt5 : PIXat m5 pixs (set_rc (hdv w h 8 0 data) 2)).
    { apply (exT_pix_livk A1 (wbytes M4 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m5 pixs _); [|exact (proj2 PMc4) | exact Lpixs_a1]. exact (PIX_wr_rc M4 pixs _ 2 PXsM4 ltac:(lia)). }
    assert (NE_pixd_pixs : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros EE; exact (NE_pixs_pixd (eq_sym EE))).
    assert (NE_cmap_pixs : Z_to_bv 64 cmap <> Z_to_bv 64 pixs) by (intros EE; rewrite EE in Lcmap_a0; rewrite Lpixs_a0 in Lcmap_a0; discriminate Lcmap_a0).
    assert (PXd5 : PIXat m5 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_patch C A1 A1 M4 m5 _ pixd pixs 64 (pixs + 20) (Z_to_le_bytes 4 2) _ CK HWs4 Lpixd_a1 Lpixs_a1 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM4 (proj2 PMc4) Lpixd_a1).
    assert (CMP5 : CMAPat m5 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_patch C A1 A1 M4 m5 _ cmap pixs 64 (pixs + 20) (Z_to_le_bytes 4 2) _ CK HWs4 Lcmap_a1 Lpixs_a1 NE_cmap_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) CMPM4 (proj2 PMc4) Lcmap_a1).
    pose proof (eq_trans (LEQ4 _) Lpixs_a1) as Lpixs_a2. pose proof (eq_trans (LEQ4 _) Ldata_a1) as Ldata_a2. pose proof (eq_trans (LEQ4 _) Lqtab_a1) as Lqtab_a2.
    pose proof (eq_trans (LEQ4 _) Lcmap_a1) as Lcmap_a2. pose proof (eq_trans (LEQ4 _) Lcmaparr_a1) as Lcmaparr_a2.
    pose proof (eq_trans (LEQ4 _) Lpixd_a1) as Lpixd_a2. pose proof (eq_trans (LEQ4 _) Ldatad_a1) as Ldatad_a2.
    assert (SUB2 : sub_live Ar A2) by (intros q0 kq Lq; rewrite LEQ4; exact (SUBr1 _ _ Lq)).
    assert (LDEL2 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad; Z_to_bv 64 qtab; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A2 q0 = live Ar q0) by (intros q0 Hq; rewrite LEQ4; exact (LDEL1 q0 Hq)).
    assert (NE_pt_datad : Z_to_bv 64 pixs <> Z_to_bv 64 datad) by exact (ne_live A0 _ _ _ Lpixs_a0 Fdatadx).
    assert (NE_pt_qtab : Z_to_bv 64 pixs <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Lpixs_a0; rewrite Lqtab_a0 in Lpixs_a0; discriminate Lpixs_a0).
    assert (RRdata : (0 <= data < 2 ^ 64)%Z) by (destruct PXs as (_ & _ & WFs & _); exact (wf_data _ WFs)).
    assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
    assert (NE_cmap_datad : Z_to_bv 64 cmap <> Z_to_bv 64 datad) by exact (ne_live A0 _ _ _ Lcmap_a0 Fdatadx).
    assert (NE_datad_qtab : Z_to_bv 64 datad <> Z_to_bv 64 qtab) by (intros EE; exact (ne_live A0 _ _ _ Lqtab_a0 Fdatadx (eq_sym EE))).
    pose proof (exW_win_blk_apart_h C A2 m5 _ s 4608 datad (4 * (wpl_of w 8 * h)) CK HW5 Ldatad_a2 Rn1 RRdatad GLO1) as WAPdatad.
    pose proof (POSTM_refl C Ar s m5) as PM5.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z)]).
  { constructor; [exact (exT_kept_patch1 C A1 _ s OFF4 4608 M4 m5 E4 (EVar 32) pixs 64 (pixs + 20) (Z_to_le_bytes 4 2) CK HWs4 Lpixs_a1 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 189%nat E4 (ex_envL vals4 r5 [data; exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [data; exW_canary SEGS 415784 m5] 189%nat ltac:(vm_cast_no_check (eq_refl 189%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [data; exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 189%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 34) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 FRs4 PMc4 CS4 OFF4 A10_4 SUB1 RM1 PMR PXsM4 PXdM4 CMPM4 CMF4 PMB LEQ4 LDEL1 PXd4 CMP4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exT_kn_pix SEGS C A2 m5 _ (ex_envL vals4 r5 [data; exW_canary SEGS 415784 m5]) (EVar 34) (EVar 32) (EVar 221) (EVar 88) pixs s 4608 _ CK HW5 Lpixs_a2 PXt5 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp5.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m5 _ (s - 4608) (Z.to_nat 4608) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [data; exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A2 m5 _ (ex_envL vals4 r5 [data; exW_canary SEGS 415784 m5]) (EVar 222) (EVar 32) (exW_canary SEGS 415784 m5) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A2 M5 (with_vmmaps vm2 md) /\ POSTM C Ar s m5 M5).
  { subst M5. apply (exW_win_blks C A2 Ar m5 _ E5 log5 (EVar 32) s 4608 [] CK HW5 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  pose proof (exW_win_only E5 m5 log5 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs5. change (mem_denot E5 m5 log5) with M5 in FRs5.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, data)]).
  exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r18 Q18_5. exW_regfactB BS5 HR ex_r9 Q9_5. exW_regfactB BS5 HR ex_r19 Q19_5. exW_regfactB BS5 HR ex_r14 Q14_5.
  clear BS5.
  (* [comment removed for export] *)
  pose (BSx5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, data)]).
  exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-128)%Z 4%nat CELLh. exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-124)%Z 4%nat CELLw.
  exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-120)%Z 8%nat CELLq.
  clear BSx5.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HLUT fxk C A2 Ar M5 _ Rc5 s w h datad data qtab S CK HWs5 SUB2 Hlo Hhi HOK Hw1 Hh1 Ldatad_a2 Fdatad F0datad Ldata_a2 Lqtab_a2 NE_datad_qtab RRdatad RRdata RRqtab
             Q2_5 Q11_5 Q18_5 Q9_5 Q19_5 Q14_5 CELLh CELLw CELLq) end.
  intros r6 m6 HW6 PMl5 AGR5 FRM5.
  assert (PM6 : POSTM C Ar s m5 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5 | exact PMl5]. }
  assert (PXd6 : PIXat m6 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_frm C A2 M5 m6 _ pixd datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) _ CK HWs5 Lpixd_a2 Ldatad_a2 NE_pixd_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A2 m5 M5 _ s 4608 pixd _ CK HW5 GLO1 Lpixd_a2 PXd5 FRs5) FRM5).
  assert (PXt6 : PIXat m6 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_frm C A2 M5 m6 _ pixs datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) _ CK HWs5 Lpixs_a2 Ldatad_a2 NE_pt_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A2 m5 M5 _ s 4608 pixs _ CK HW5 GLO1 Lpixs_a2 PXt5 FRs5) FRM5).
  assert (CMP6 : CMAPat m6 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_frm C A2 M5 m6 _ cmap datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) _ CK HWs5 Lcmap_a2 Ldatad_a2 NE_cmap_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_cmap_sess C A2 m5 M5 _ s 4608 cmap _ CK HW5 GLO1 Lcmap_a2 CMP5 FRs5) FRM5).
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, (-4608)%Z, (-4608 + 4608)%Z)]).
  { constructor; [exact (exW_kept_frame E5 M5 m6 (EVar 32) s (-4608) 4608 datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) FRM5 eq_refl RS WAPdatad (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 223%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_keep _ _ _ _ _ [5%nat; 6%nat; 7%nat; 8%nat; 10%nat; 11%nat; 12%nat; 13%nat; 15%nat; 16%nat; 17%nat; 20%nat; 22%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 415784 m6] 223%nat ltac:(vm_cast_no_check (eq_refl 223%nat))) (exW_agree_keep _ _ _ AGR5)) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 223%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 223%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ fr2 (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q2_5 Q11_5 Q18_5 Q9_5 Q19_5 Q14_5 PM5 HW5 FRs5 AGR5 FRM5 PMl5 CELLh CELLw CELLq PXd5 PXt5 CMP5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m6 _ (s - 4608) (Z.to_nat 4608) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A2 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) (EVar 255) (EVar 32) (exW_canary SEGS 415784 m6) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  assert (NE_pixd_qtab : Z_to_bv 64 pixd <> Z_to_bv 64 qtab) by (intros EE; exact (ne_live A0 _ _ _ Lqtab_a0 Fpixdx (eq_sym EE))).
  assert (NE_cmap_qtab : Z_to_bv 64 cmap <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Lcmap_a0; rewrite Lqtab_a0 in Lcmap_a0; discriminate Lcmap_a0).
  (* [comment removed for export] *)
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A2 M6 (with_vmmaps vm2 md) /\ POSTM C Ar s m6 M6).
  { subst M6. apply (exW_win_blks C A2 Ar m6 _ E6 log6 (EVar 32) s 4608 [] CK HW6 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  pose proof (exW_win_only E6 m6 log6 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs6. change (mem_denot E6 m6 log6) with M6 in FRs6.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (35%nat, w); (36%nat, h); (50%nat, qtab); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, data)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A2 M6 _ Rc6 (Z_to_bv 64 qtab) (Z_to_bv 64 ret) 1024 sp' S CK HWs6 Q10_6 Lqtab_a2 F0qtab Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m7 vm3 r7 HW7 CSx6 Ldead6 LEQ6 PMc6 RTR6.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (SUB3 : sub_live Ar A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 qtab) by (intros ->; rewrite Fqtab in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB2 q kq Lq). }
  assert (PM7 : POSTM C Ar s m5 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C Ar A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  pose proof (RTR6 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  pose proof (eq_trans (LEQ6 _ NE_pixd_qtab) Lpixd_a2) as Lpixd_a3.
  pose proof (eq_trans (LEQ6 _ NE_datad_qtab) Ldatad_a2) as Ldatad_a3.
  pose proof (eq_trans (LEQ6 _ NE_cmap_qtab) Lcmap_a2) as Lcmap_a3.
  pose proof (eq_trans (LEQ6 _ NE_cmaparr_qtab) Lcmaparr_a2) as Lcmaparr_a3.
  pose proof (eq_trans (LEQ6 _ NE_pt_qtab) Lpixs_a2) as Lpixs_a3.
  assert (LDEL3 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A3 q0 = live Ar q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 qtab = q0)) as [<-|NEq]; [rewrite Ldead6, Fqtab; reflexivity|]. rewrite (LEQ6 q0 (fun EE => NEq (eq_sym EE))). apply LDEL2. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (PXd7 : PIXat m7 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_livk A3 M6 m7 pixd _ (exT_pix_sess C A2 m6 M6 _ s 4608 pixd _ CK HW6 GLO1 Lpixd_a2 PXd6 FRs6) (proj2 PMc6) Lpixd_a3).
  assert (PXt7 : PIXat m7 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_livk A3 M6 m7 pixs _ (exT_pix_sess C A2 m6 M6 _ s 4608 pixs _ CK HW6 GLO1 Lpixs_a2 PXt6 FRs6) (proj2 PMc6) Lpixs_a3).
  assert (CMP7 : CMAPat m7 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_livk A3 M6 m7 cmap _ (exT_cmap_sess C A2 m6 M6 _ s 4608 cmap _ CK HW6 GLO1 Lcmap_a2 CMP6 FRs6) (proj2 PMc6) Lcmap_a3).
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 4608 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [50%nat] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 256%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 415784 m7] 256%nat ltac:(vm_cast_no_check (eq_refl 256%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) m7 _) by (exact (know_ok_agree SEGS 256%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 256%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ fr2 (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q1_6 Q2_6 Q4_6 PM6 HW6 FRs6 LDEL2 PXd6 PXt6 CMP6 Lpixd_a2 Ldatad_a2 Lcmap_a2 Lcmaparr_a2 Lpixs_a2 PMc6 CS6 SUB2 RM2 Ldead6 LEQ6 RTR6 Lqtab_a2 OFF6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m7 _ (s - 4608) (Z.to_nat 4608) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 415784 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m7]).
  pose proof (exW_kn_fixed SEGS C A3 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) (EVar 288) (EVar 32) (exW_canary SEGS 415784 m7) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A3 M7 (with_vmmaps vm3 md) /\ POSTM C Ar s m7 M7).
  { subst M7. apply (exW_win_blks C A3 Ar m7 _ E7 log7 (EVar 32) s 4608 [] CK HW7 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  pose proof (exW_win_only E7 m7 log7 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs7. change (mem_denot E7 m7 log7) with M7 in FRs7.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, data)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  (* [comment removed for export] *)
  pose (BSx7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, data)]).
  exW_cellB HK Hlf r0 BSx7 (EVar 32) s (-152)%Z 8%nat CELLpp.
  clear BSx7.
  assert (PXdM7 : PIXat M7 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_sess C A3 m7 M7 _ s 4608 pixd _ CK HW7 GLO1 Lpixd_a3 PXd7 FRs7).
  assert (PXtM7 : PIXat M7 pixs (set_rc (hdv w h 8 0 data) 2)) by exact (exT_pix_sess C A3 m7 M7 _ s 4608 pixs _ CK HW7 GLO1 Lpixs_a3 PXt7 FRs7).
  assert (CMPM7 : CMAPat M7 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_sess C A3 m7 M7 _ s 4608 cmap _ CK HW7 GLO1 Lcmap_a3 CMP7 FRs7).
  assert (PPlo : (s + OFF7 <= s + -152)%Z) by (unfold OFF7; lia). assert (PPhi : (s + -152 + 8 <= c_top C)%Z) by lia.
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HRC2 fxk C A3 M7 _ Rc7 (s + OFF7)%Z (s + -152)%Z pixs (set_rc (hdv w h 8 0 data) 2) (Z_to_bv 64 ra) S CK HWs7 Q2_7
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF7, PXD2_STACK, ALLOC_STACK; lia) PPlo PPhi ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q1_7 ltac:(red; apply bv_eq; reflexivity) Q10_7 CELLpp
             PXtM7 eq_refl Lpixs_a3 F0pixs) end end.
  intros m8 r8 HW8 CSx7 PMD.
  pose proof CSx7 as CS7. clear CSx7.
  assert (PMB8 : POSTM C Ar s m0 m8).
  { apply (CLONEK A3 M7 m8 _ (s + -152)%Z HWs7 SUB3 ltac:(lia) ltac:(lia) ltac:(lia) (POSTM_trans _ _ _ _ _ _ PM7 PMs7) PMD). }
  assert (PXd8 : PIXat m8 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_patch2 C A3 A3 M7 m8 _ pixd pixs 64 (pixs + 20) (s + -152) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs7 Lpixd_a3 Lpixs_a3 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM7 (proj2 PMD) Lpixd_a3).
  assert (CMP8 : CMAPat m8 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_patch2 C A3 A3 M7 m8 _ cmap pixs 64 (pixs + 20) (s + -152) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs7 Lcmap_a3 Lpixs_a3 NE_cmap_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) CMPM7 (proj2 PMD) Lcmap_a3).
  assert (FRMx7 : FRM C (s + -144) (wbytes (wbytes M7 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 (s + -152)) (Z_to_le_bytes 8 0)) m8).
  { replace (s + -144)%Z with (s + -152 + 8)%Z by lia. exact (proj1 PMD). }
  pose proof (POSTM_refl C Ar s m8) as PM8.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, (-144)%Z, 0%Z)]).
  { constructor; [exact (exT_kept_patch2 C A3 _ s (-144) 4608 M7 m8 E7 (EVar 32) pixs 64 (pixs + 20) (s + -152) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) CK HWs7 Lpixs_a3 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) FRMx7 Hlo Hhi eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia))|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [50%nat] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 289%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [exW_canary SEGS 415784 m8] 289%nat ltac:(vm_cast_no_check (eq_refl 289%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) m8 _) by (exact (know_ok_agree SEGS 289%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 289%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ fr2 (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q1_7 Q2_7 Q4_7 PM7 HW7 FRs7 CS7 OFF7 CELLpp PXdM7 PXtM7 CMPM7 PPlo PPhi PXd7 PXt7 CMP7 PMD FRMx7 CLONEK.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m8 _ (s - 4608) (Z.to_nat 4608) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 415784 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m8]).
  pose proof (exW_kn_fixed SEGS C A3 m8 _ (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) (EVar 321) (EVar 32) (exW_canary SEGS 415784 m8) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A3 M8 (with_vmmaps vm3 md) /\ POSTM C Ar s m8 M8).
  { subst M8. apply (exW_win_blks C A3 Ar m8 _ E8 log8 (EVar 32) s 4608 [] CK HW8 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  pose proof (exW_win_only E8 m8 log8 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs8. change (mem_denot E8 m8 log8) with M8 in FRs8.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, data)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A3 M8 vm3 RcF FZ HWs8) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exT_cs_of_al EE sr regsE RcF [(2%nat, EVar 32); (3%nat, EVar 3); (4%nat, ELit 284096); (8%nat, EVar 38); (9%nat, EVar 39); (18%nat, EVar 40); (19%nat, EVar 41); (20%nat, EVar 42); (21%nat, EVar 43); (22%nat, EVar 44); (23%nat, EVar 45); (24%nat, EVar 46); (25%nat, EVar 47); (26%nat, EVar 48); (27%nat, EVar 49)] HR) end.
    { constructor; [symmetry; exact HE2k|]. constructor; [exact HG3|]. constructor; [symmetry; exact HE4k|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor. }
    { vm_compute; reflexivity. }
  + exact (POSTM_trans _ _ _ _ _ _ PMB8 PMs8).
  + exists pixd, datad. split; [exact G10|].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a3 (conj Ldatad_a3 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A3 m8 M8 _ s 4608 pixd _ CK HW8 GLO1 Lpixd_a3 PXd8 FRs8).
    * right. exists cmaparr.
      refine (conj CMOK (conj Gcm1 (conj Gcm2 (conj Gca1 (conj Gca2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj Fcmap (conj Fcmaparr (conj F0cmap (conj F0cmaparr (conj Lcmap_a3 (conj Lcmaparr_a3 (conj _ _))))))))))))))))).
      -- intros EE. rewrite EE in Lcmap_a0. rewrite Lcmaparr_a0 in Lcmap_a0. discriminate Lcmap_a0.
      -- intros EE. apply NE_pixd_cmap. rewrite EE. reflexivity.
      -- intros EE. apply NE_cmap_datad. rewrite EE. reflexivity.
      -- intros EE. exact (ne_live A0 _ _ _ Lcmaparr_a0 Fpixdx (f_equal (Z_to_bv 64) EE)).
      -- intros EE. exact (ne_live A0 _ _ _ Lcmaparr_a0 Fdatadx (f_equal (Z_to_bv 64) EE)).
      -- exact (exT_cmap_sess C A3 m8 M8 _ s 4608 cmap _ CK HW8 GLO1 Lcmap_a3 CMP8 FRs8).
      -- intros q0 N1 N2 N3 N4. apply LDEL3. clear - N1 N2 N3 N4. cbn [In]. intros [EE|[EE|[EE|[EE|[]]]]]; [apply N1 | apply N2 | apply N4 | apply N3]; symmetry; exact EE.
  + exact RM3.
  - (* [comment removed for export] *)
    destruct PTN as (Gpt1 & Gpt2 & ALpixt & Gdt1 & Gdt2 & ALdatat & NEptdt & Fpixtx & Fdatatx & F0pixt & F0datat & Lpixt_a2 & Ldatat_a2 & PXt5 & CMR).
    destruct CMR as [(_ & LEQ4) | (ad & _ & XX & _)]; [|exfalso; apply XX; reflexivity].
    assert (RRpixt : (0 <= pixt < 2 ^ 64)%Z) by lia. assert (RRdatat : (0 <= datat < 2 ^ 64)%Z) by lia.
    assert (PMB5 : POSTM C Ar s m0 m5).
    { eapply POSTM_trans; [exact PMB|]. apply (POSTM_sub C Ar A1 _ _ _ SUBr1). apply (POSTM_mono C A1 (s + OFF4) s); [unfold OFF4; lia | exact PMc4]. }
    assert (PXd5 : PIXat m5 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_livk A1 M4 m5 pixd _ PXdM4 (proj2 PMc4) Lpixd_a1).
    assert (CMP5 : CMAPat m5 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_livk A1 M4 m5 cmap _ CMPM4 (proj2 PMc4) Lcmap_a1).
    pose proof (eq_trans (LEQ4 _ (ne_live A1 _ _ _ Lqtab_a1 Fpixtx) (ne_live A1 _ _ _ Lqtab_a1 Fdatatx)) Lqtab_a1) as Lqtab_a2.
    pose proof (eq_trans (LEQ4 _ (ne_live A1 _ _ _ Lcmap_a1 Fpixtx) (ne_live A1 _ _ _ Lcmap_a1 Fdatatx)) Lcmap_a1) as Lcmap_a2.
    pose proof (eq_trans (LEQ4 _ (ne_live A1 _ _ _ Lcmaparr_a1 Fpixtx) (ne_live A1 _ _ _ Lcmaparr_a1 Fdatatx)) Lcmaparr_a1) as Lcmaparr_a2.
    pose proof (eq_trans (LEQ4 _ (ne_live A1 _ _ _ Lpixd_a1 Fpixtx) (ne_live A1 _ _ _ Lpixd_a1 Fdatatx)) Lpixd_a1) as Lpixd_a2.
    pose proof (eq_trans (LEQ4 _ (ne_live A1 _ _ _ Ldatad_a1 Fpixtx) (ne_live A1 _ _ _ Ldatad_a1 Fdatatx)) Ldatad_a1) as Ldatad_a2.
    assert (SUB2 : sub_live Ar A2).
    { intros q0 kq Lq. pose proof (SUBr1 _ _ Lq) as L1. rewrite (LEQ4 q0 (ne_live A1 q0 _ kq L1 Fpixtx) (ne_live A1 q0 _ kq L1 Fdatatx)). exact L1. }
    pose proof (fresh_sub Ar A1 _ SUBr1 Fpixtx) as Fpixt. pose proof (fresh_sub Ar A1 _ SUBr1 Fdatatx) as Fdatat.
    assert (LDEL2 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad; Z_to_bv 64 qtab; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A2 q0 = live Ar q0).
    { intros q0 Hq. rewrite (LEQ4 q0 (fun EE => Hq (or_introl (eq_sym EE))) (fun EE => Hq (or_intror (or_introl (eq_sym EE))))). apply LDEL1. intros XX. apply Hq. right; right; exact XX. }
    assert (NE_pt_datad : Z_to_bv 64 pixt <> Z_to_bv 64 datad) by (intros EE; exact (ne_live A1 _ _ _ Ldatad_a1 Fpixtx (eq_sym EE))).
    assert (NE_pt_qtab : Z_to_bv 64 pixt <> Z_to_bv 64 qtab) by (intros EE; exact (ne_live A1 _ _ _ Lqtab_a1 Fpixtx (eq_sym EE))).
    assert (NE_dt_qtab : Z_to_bv 64 datat <> Z_to_bv 64 qtab) by (intros EE; exact (ne_live A1 _ _ _ Lqtab_a1 Fdatatx (eq_sym EE))).
    assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
    assert (NE_cmap_datad : Z_to_bv 64 cmap <> Z_to_bv 64 datad) by exact (ne_live A0 _ _ _ Lcmap_a0 Fdatadx).
    assert (NE_datad_qtab : Z_to_bv 64 datad <> Z_to_bv 64 qtab) by (intros EE; exact (ne_live A0 _ _ _ Lqtab_a0 Fdatadx (eq_sym EE))).
    pose proof (exW_win_blk_apart_h C A2 m5 _ s 4608 datad (4 * (wpl_of w 8 * h)) CK HW5 Ldatad_a2 Rn1 RRdatad GLO1) as WAPdatad.
    pose proof (POSTM_refl C Ar s m5) as PM5.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, OFF4, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF4 4608 M4 m5 E4 (EVar 32) CK (proj1 PMc4) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 189%nat E4 (ex_envL vals4 r5 [pixt; datat; exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [pixt; datat; exW_canary SEGS 415784 m5] 189%nat ltac:(vm_cast_no_check (eq_refl 189%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [pixt; datat; exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 189%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  pose proof (ex_regs_ok_reexpr _ _ r5 ex_r10 (EVar 221) HRn5 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_4)) as HRx5. clear HRn5. rename HRx5 into HRn5.
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q10_4 Q11_4 Q1_4 Q2_4 Q4_4 PM4 HW4 FRs4 PMc4 CS4 OFF4 A10_4 SUB1 RM1 PXsM4 PXdM4 CMPM4 CMF4 PMB LEQ4 LDEL1 PXd4 CMP4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (exT_kn_pix SEGS C A2 m5 _ (ex_envL vals4 r5 [pixt; datat; exW_canary SEGS 415784 m5]) (EVar 221) (EVar 32) (EVar 222) (EVar 88) pixt s 4608 _ CK HW5 Lpixt_a2 PXt5 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp5.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m5 _ (s - 4608) (Z.to_nat 4608) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [pixt; datat; exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A2 m5 _ (ex_envL vals4 r5 [pixt; datat; exW_canary SEGS 415784 m5]) (EVar 223) (EVar 32) (exW_canary SEGS 415784 m5) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A2 M5 (with_vmmaps vm2 md) /\ POSTM C Ar s m5 M5).
  { subst M5. apply (exW_win_blks C A2 Ar m5 _ E5 log5 (EVar 32) s 4608 [] CK HW5 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  pose proof (exW_win_only E5 m5 log5 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs5. change (mem_denot E5 m5 log5) with M5 in FRs5.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, pixt); (222%nat, datat)]).
  exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r18 Q18_5. exW_regfactB BS5 HR ex_r9 Q9_5. exW_regfactB BS5 HR ex_r19 Q19_5. exW_regfactB BS5 HR ex_r14 Q14_5.
  clear BS5.
  (* [comment removed for export] *)
  pose (BSx5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, pixt); (222%nat, datat)]).
  exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-128)%Z 4%nat CELLh. exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-124)%Z 4%nat CELLw.
  exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-120)%Z 8%nat CELLq.
  clear BSx5.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HLUT fxk C A2 Ar M5 _ Rc5 s w h datad datat qtab S CK HWs5 SUB2 Hlo Hhi HOK Hw1 Hh1 Ldatad_a2 Fdatad F0datad Ldatat_a2 Lqtab_a2 NE_datad_qtab RRdatad RRdatat RRqtab
             Q2_5 Q11_5 Q18_5 Q9_5 Q19_5 Q14_5 CELLh CELLw CELLq) end.
  intros r6 m6 HW6 PMl5 AGR5 FRM5.
  assert (PM6 : POSTM C Ar s m5 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5 | exact PMl5]. }
  assert (PXd6 : PIXat m6 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_frm C A2 M5 m6 _ pixd datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) _ CK HWs5 Lpixd_a2 Ldatad_a2 NE_pixd_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A2 m5 M5 _ s 4608 pixd _ CK HW5 GLO1 Lpixd_a2 PXd5 FRs5) FRM5).
  assert (PXt6 : PIXat m6 pixt (hdv w h 8 0 datat)) by exact (exT_pix_frm C A2 M5 m6 _ pixt datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) _ CK HWs5 Lpixt_a2 Ldatad_a2 NE_pt_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A2 m5 M5 _ s 4608 pixt _ CK HW5 GLO1 Lpixt_a2 PXt5 FRs5) FRM5).
  assert (CMP6 : CMAPat m6 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_frm C A2 M5 m6 _ cmap datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) _ CK HWs5 Lcmap_a2 Ldatad_a2 NE_cmap_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_cmap_sess C A2 m5 M5 _ s 4608 cmap _ CK HW5 GLO1 Lcmap_a2 CMP5 FRs5) FRM5).
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, (-4608)%Z, (-4608 + 4608)%Z)]).
  { constructor; [exact (exW_kept_frame E5 M5 m6 (EVar 32) s (-4608) 4608 datad (4 * (wpl_of w 8 * h)) datad (datad + 4 * (wpl_of w 8 * h)) FRM5 eq_refl RS WAPdatad (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 224%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_keep _ _ _ _ _ [5%nat; 6%nat; 7%nat; 8%nat; 10%nat; 11%nat; 12%nat; 13%nat; 15%nat; 16%nat; 17%nat; 20%nat; 22%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 415784 m6] 224%nat ltac:(vm_cast_no_check (eq_refl 224%nat))) (exW_agree_keep _ _ _ AGR5)) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 224%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 224%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ fr2 (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q2_5 Q11_5 Q18_5 Q9_5 Q19_5 Q14_5 PM5 HW5 FRs5 AGR5 FRM5 PMl5 CELLh CELLw CELLq PXd5 PXt5 CMP5.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A2 m6 _ (s - 4608) (Z.to_nat 4608) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A2 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) (EVar 256) (EVar 32) (exW_canary SEGS 415784 m6) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  assert (NE_pixd_qtab : Z_to_bv 64 pixd <> Z_to_bv 64 qtab) by (intros EE; exact (ne_live A0 _ _ _ Lqtab_a0 Fpixdx (eq_sym EE))).
  assert (NE_cmap_qtab : Z_to_bv 64 cmap <> Z_to_bv 64 qtab) by (intros EE; rewrite EE in Lcmap_a0; rewrite Lqtab_a0 in Lcmap_a0; discriminate Lcmap_a0).
  (* [comment removed for export] *)
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A2 M6 (with_vmmaps vm2 md) /\ POSTM C Ar s m6 M6).
  { subst M6. apply (exW_win_blks C A2 Ar m6 _ E6 log6 (EVar 32) s 4608 [] CK HW6 SUB2 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  pose proof (exW_win_only E6 m6 log6 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs6. change (mem_denot E6 m6 log6) with M6 in FRs6.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BS6 := [(32%nat, s); (35%nat, w); (36%nat, h); (50%nat, qtab); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, pixt); (222%nat, datat)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  (* [comment removed for export] *)
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A2 M6 _ Rc6 (Z_to_bv 64 qtab) (Z_to_bv 64 ret) 1024 sp' S CK HWs6 Q10_6 Lqtab_a2 F0qtab Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A3 m7 vm3 r7 HW7 CSx6 Ldead6 LEQ6 PMc6 RTR6.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (SUB3 : sub_live Ar A3).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 qtab) by (intros ->; rewrite Fqtab in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB2 q kq Lq). }
  assert (PM7 : POSTM C Ar s m5 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C Ar A3 _ _ _ SUB3).
    apply (POSTM_mono C A3 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  pose proof (RTR6 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(lia) ltac:(lia)) as RM3. rewrite !Z.sub_0_r in RM3.
  pose proof (eq_trans (LEQ6 _ NE_pixd_qtab) Lpixd_a2) as Lpixd_a3.
  pose proof (eq_trans (LEQ6 _ NE_datad_qtab) Ldatad_a2) as Ldatad_a3.
  pose proof (eq_trans (LEQ6 _ NE_cmap_qtab) Lcmap_a2) as Lcmap_a3.
  pose proof (eq_trans (LEQ6 _ NE_cmaparr_qtab) Lcmaparr_a2) as Lcmaparr_a3.
  pose proof (eq_trans (LEQ6 _ NE_pt_qtab) Lpixt_a2) as Lpixt_a3.
  pose proof (eq_trans (LEQ6 _ NE_dt_qtab) Ldatat_a2) as Ldatat_a3.
  assert (LDEL3 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixt; Z_to_bv 64 datat; Z_to_bv 64 pixd; Z_to_bv 64 datad; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A3 q0 = live Ar q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 qtab = q0)) as [<-|NEq]; [rewrite Ldead6, Fqtab; reflexivity|]. rewrite (LEQ6 q0 (fun EE => NEq (eq_sym EE))). apply LDEL2. clear - Hq NEq. cbn [In] in *. tauto. }
  assert (PXd7 : PIXat m7 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_livk A3 M6 m7 pixd _ (exT_pix_sess C A2 m6 M6 _ s 4608 pixd _ CK HW6 GLO1 Lpixd_a2 PXd6 FRs6) (proj2 PMc6) Lpixd_a3).
  assert (PXt7 : PIXat m7 pixt (hdv w h 8 0 datat)) by exact (exT_pix_livk A3 M6 m7 pixt _ (exT_pix_sess C A2 m6 M6 _ s 4608 pixt _ CK HW6 GLO1 Lpixt_a2 PXt6 FRs6) (proj2 PMc6) Lpixt_a3).
  assert (CMP7 : CMAPat m7 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_livk A3 M6 m7 cmap _ (exT_cmap_sess C A2 m6 M6 _ s 4608 cmap _ CK HW6 GLO1 Lcmap_a2 CMP6 FRs6) (proj2 PMc6) Lcmap_a3).
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 4608 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [50%nat] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose proof (regs_ok_agree 257%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 415784 m7] 257%nat ltac:(vm_cast_no_check (eq_refl 257%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) m7 _) by (exact (know_ok_agree SEGS 257%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  rewrite (fr_denot_agree 257%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) _ fr2 (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 Q10_6 Q1_6 Q2_6 Q4_6 PM6 HW6 FRs6 LDEL2 PXd6 PXt6 CMP6 Lpixd_a2 Ldatad_a2 Lcmap_a2 Lcmaparr_a2 Lpixt_a2 Ldatat_a2 PMc6 CS6 SUB2 RM2 Ldead6 LEQ6 RTR6 Lqtab_a2 OFF6.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A3 m7 _ (s - 4608) (Z.to_nat 4608) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 415784 m7 (canary_any m7)) as CANOK7.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m7]).
  pose proof (exW_kn_fixed SEGS C A3 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 415784 m7]) (EVar 289) (EVar 32) (exW_canary SEGS 415784 m7) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A3 M7 (with_vmmaps vm3 md) /\ POSTM C Ar s m7 M7).
  { subst M7. apply (exW_win_blks C A3 Ar m7 _ E7 log7 (EVar 32) s 4608 [] CK HW7 SUB3 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP7 as [HWs7 PMs7].
  pose proof (exW_win_only E7 m7 log7 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs7. change (mem_denot E7 m7 log7) with M7 in FRs7.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose (BS7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, pixt); (222%nat, datat)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r1 Q1_7. exW_regfactB BS7 HR ex_r2 Q2_7. exW_regfactB BS7 HR ex_r4 Q4_7.
  clear BS7.
  lazymatch type of Q2_7 with _ = Z_to_bv 64 (s + ?off) => pose (OFF7 := off) end.
  (* [comment removed for export] *)
  pose (BSx7 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, pixt); (222%nat, datat)]).
  exW_cellB HK Hlf r0 BSx7 (EVar 32) s (-152)%Z 8%nat CELLpp.
  clear BSx7.
  assert (PXdM7 : PIXat M7 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_sess C A3 m7 M7 _ s 4608 pixd _ CK HW7 GLO1 Lpixd_a3 PXd7 FRs7).
  assert (PXtM7 : PIXat M7 pixt (hdv w h 8 0 datat)) by exact (exT_pix_sess C A3 m7 M7 _ s 4608 pixt _ CK HW7 GLO1 Lpixt_a3 PXt7 FRs7).
  assert (CMPM7 : CMAPat M7 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_sess C A3 m7 M7 _ s 4608 cmap _ CK HW7 GLO1 Lcmap_a3 CMP7 FRs7).
  assert (PPlo : (s + OFF7 <= s + -152)%Z) by (unfold OFF7; lia). assert (PPhi : (s + -152 + 8 <= c_top C)%Z) by lia.
  rewrite PC_DESTROY_eq.
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixDestroy_keep_W (fx := fxk) C A3 M7 _ Rc7 (s + OFF7) (s + -152) pixt 0 0 (4 * (wpl_of w 8 * h)) (hdv w h 8 0 datat) cv (Z_to_bv 64 ra) S CK HWs7 Q2_7
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF7, ALLOC_STACK; lia) PPlo PPhi Q1_7 ltac:(red; apply bv_eq; reflexivity) Q4_7 ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q10_7 CELLpp
             PXtM7 eq_refl eq_refl eq_refl Lpixt_a3 F0pixt Ldatat_a3 F0datat Rn1 (fun EE => NEptdt (eq_sym EE)) (or_introl eq_refl)) end end.
  intros A4 m8 vm4 r8 HW8 CSx7 PDP PMc7 CELL0 FRMs7 RTR7.
  pose proof CSx7 as CS7. clear CSx7.
  rewrite with_vmmaps_twice in HW8 |- *.
  destruct PDP as (Dpixt & Ddatat & _ & LEQ7). change (p_data (hdv w h 8 0 datat)) with datat in Ddatat, LEQ7.
  assert (NZdatat : datat <> 0%Z) by lia.
  pose proof (fun (q0 : word) (N1 : q0 <> Z_to_bv 64 pixt) (N2 : q0 <> Z_to_bv 64 datat) => LEQ7 q0 N1 (fun _ => N2) (fun XX : 0%Z <> 0%Z => False_ind _ (XX eq_refl))) as LEQx7.
  pose proof (eq_trans (LEQx7 _ (ne_live A1 _ _ _ Lpixd_a1 Fpixtx) (ne_live A1 _ _ _ Lpixd_a1 Fdatatx)) Lpixd_a3) as Lpixd_a4.
  pose proof (eq_trans (LEQx7 _ (ne_live A1 _ _ _ Ldatad_a1 Fpixtx) (ne_live A1 _ _ _ Ldatad_a1 Fdatatx)) Ldatad_a3) as Ldatad_a4.
  pose proof (eq_trans (LEQx7 _ (ne_live A1 _ _ _ Lcmap_a1 Fpixtx) (ne_live A1 _ _ _ Lcmap_a1 Fdatatx)) Lcmap_a3) as Lcmap_a4.
  pose proof (eq_trans (LEQx7 _ (ne_live A1 _ _ _ Lcmaparr_a1 Fpixtx) (ne_live A1 _ _ _ Lcmaparr_a1 Fdatatx)) Lcmaparr_a3) as Lcmaparr_a4.
  assert (SUB4 : sub_live Ar A4).
  { intros q0 kq Lq. rewrite (LEQx7 q0 (ne_live Ar q0 _ kq Lq Fpixt) (ne_live Ar q0 _ kq Lq Fdatat)). exact (SUB3 _ _ Lq). }
  assert (LDEL4 : forall q0 : word, ~ In q0 [Z_to_bv 64 pixd; Z_to_bv 64 datad; Z_to_bv 64 cmaparr; Z_to_bv 64 cmap] -> live A4 q0 = live Ar q0).
  { intros q0 Hq. destruct (decide (Z_to_bv 64 pixt = q0)) as [<-|NEq1]; [rewrite Dpixt, Fpixt; reflexivity|].
    destruct (decide (Z_to_bv 64 datat = q0)) as [<-|NEq2]; [rewrite (Ddatat NZdatat), Fdatat; reflexivity|].
    rewrite (LEQx7 q0 (fun EE => NEq1 (eq_sym EE)) (fun EE => NEq2 (eq_sym EE))). apply LDEL3. clear - Hq NEq1 NEq2. cbn [In] in *. tauto. }
  pose proof (RTR7 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR; lia) ltac:(clear - HbR; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  assert (PMB8 : POSTM C Ar s m0 m8).
  { eapply POSTM_trans; [exact PMB5|]. eapply POSTM_trans; [exact (POSTM_trans _ _ _ _ _ _ PM7 PMs7)|]. apply (POSTM_sub C Ar A4 _ _ _ SUB4). apply (POSTM_mono C A4 (s + -152 + 8) s); [lia | exact PMc7]. }
  assert (PXd8 : PIXat m8 pixd (set_cmap (set_data (pix_hdr w h 8) datad) cmap)) by exact (exT_pix_livk A4 M7 m8 pixd _ PXdM7 (proj2 PMc7) Lpixd_a4).
  assert (CMP8 : CMAPat m8 cmap (CMAPV cmaparr 8 256 5 0)) by exact (exT_cmap_livk A4 M7 m8 cmap _ CMPM7 (proj2 PMc7) Lcmap_a4).
  assert (FRMx7 : FRM C (s + -144) M7 m8).
  { replace (s + -144)%Z with (s + -152 + 8)%Z by lia. exact (proj1 PMc7). }
  pose proof (POSTM_refl C Ar s m8) as PM8.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, (-144)%Z, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s (-144) 4608 M7 m8 E7 (EVar 32) CK FRMx7 Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [50%nat] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose proof (regs_ok_agree 290%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [exW_canary SEGS 415784 m8] 290%nat ltac:(vm_cast_no_check (eq_refl 290%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) m8 _) by (exact (know_ok_agree SEGS 290%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  rewrite (fr_denot_agree 290%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) _ fr2 (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 Q10_7 Q1_7 Q2_7 Q4_7 PM7 HW7 FRs7 CS7 OFF7 CELLpp PXdM7 PXtM7 CMPM7 PPlo PPhi PXd7 PXt7 CMP7 PMc7 FRMx7 CELL0 FRMs7 RTR7 LEQ7 LEQx7 LDEL3 PMB5 RM3.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A4 m8 _ (s - 4608) (Z.to_nat 4608) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 415784 m8 (canary_any m8)) as CANOK8.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m8]).
  pose proof (exW_kn_fixed SEGS C A4 m8 _ (ex_envL vals7 r8 [exW_canary SEGS 415784 m8]) (EVar 322) (EVar 32) (exW_canary SEGS 415784 m8) s 4608 415784 65536 212992 213416 213568 213416 213568
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A4 M8 (with_vmmaps vm4 md) /\ POSTM C Ar s m8 M8).
  { subst M8. apply (exW_win_blks C A4 Ar m8 _ E8 log8 (EVar 32) s 4608 [] CK HW8 SUB4 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP8 as [HWs8 PMs8].
  pose proof (exW_win_only E8 m8 log8 (EVar 32) s 4608 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs8. change (mem_denot E8 m8 log8) with M8 in FRs8.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (50%nat, qtab); (51%nat, cmap); (52%nat, cmaparr); (86%nat, pixd); (87%nat, datad); (88%nat, wpl_of w 8); (221%nat, pixt); (222%nat, datat)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A4 M8 vm4 RcF FZ HWs8) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exT_cs_of_al EE sr regsE RcF [(2%nat, EVar 32); (3%nat, EVar 3); (4%nat, ELit 284096); (8%nat, EVar 38); (9%nat, EVar 39); (18%nat, EVar 40); (19%nat, EVar 41); (20%nat, EVar 42); (21%nat, EVar 43); (22%nat, EVar 44); (23%nat, EVar 45); (24%nat, EVar 46); (25%nat, EVar 47); (26%nat, EVar 48); (27%nat, EVar 49)] HR) end.
    { constructor; [symmetry; exact HE2k|]. constructor; [exact HG3|]. constructor; [symmetry; exact HE4k|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor. }
    { vm_compute; reflexivity. }
  + exact (POSTM_trans _ _ _ _ _ _ PMB8 PMs8).
  + exists pixd, datad. split; [exact G10|].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a4 (conj Ldatad_a4 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A4 m8 M8 _ s 4608 pixd _ CK HW8 GLO1 Lpixd_a4 PXd8 FRs8).
    * right. exists cmaparr.
      refine (conj CMOK (conj Gcm1 (conj Gcm2 (conj Gca1 (conj Gca2 (conj _ (conj _ (conj _ (conj _ (conj _ (conj Fcmap (conj Fcmaparr (conj F0cmap (conj F0cmaparr (conj Lcmap_a4 (conj Lcmaparr_a4 (conj _ _))))))))))))))))).
      -- intros EE. rewrite EE in Lcmap_a0. rewrite Lcmaparr_a0 in Lcmap_a0. discriminate Lcmap_a0.
      -- intros EE. apply NE_pixd_cmap. rewrite EE. reflexivity.
      -- intros EE. apply NE_cmap_datad. rewrite EE. reflexivity.
      -- intros EE. exact (ne_live A0 _ _ _ Lcmaparr_a0 Fpixdx (f_equal (Z_to_bv 64) EE)).
      -- intros EE. exact (ne_live A0 _ _ _ Lcmaparr_a0 Fdatadx (f_equal (Z_to_bv 64) EE)).
      -- exact (exT_cmap_sess C A4 m8 M8 _ s 4608 cmap _ CK HW8 GLO1 Lcmap_a4 CMP8 FRs8).
      -- intros q0 N1 N2 N3 N4. apply LDEL4. clear - N1 N2 N3 N4. cbn [In]. intros [EE|[EE|[EE|[EE|[]]]]]; [apply N1 | apply N2 | apply N4 | apply N3]; symmetry; exact EE.
  + exact RM4.
Qed.
End Tail.
End Chain.
