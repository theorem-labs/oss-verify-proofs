(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptMorphSeqA O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptCloseSpec O23LeptMorphSeqB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23Memset V23LeptStrlenH V23LeptMorphSeqA V23LeptStderr V23LeptPixHdr V23LeptCmapValid V23LeptPixCopyT V23LeptPixCopyST V23LeptMbc V23LeptCloseSpec V23LeptMorphSeqB V23ExecUb.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptExecT LeptArith LeptRoomPC LeptRoom14 LeptRoomBL LeptExecB.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.
Lemma mseqt_sltu_ge : forall p q : Z, (0 <= q <= p)%Z -> (p < 2 ^ 64)%Z -> alu64 ALU_SLTU (Z_to_bv 64 p) (Z_to_bv 64 q) = Z_to_bv 64 0.
Proof. intros p q Hq Hp. rewrite alu_sltu, WalksLib.v_sltu_Z by lia. rewrite (proj2 (Z.ltb_ge p q)) by lia. reflexivity. Qed.
Lemma mseqt_sl_cs : forall regs regs' : bvmap 5 word, regs_agree (fun r => In r sl_clob) regs regs' -> cs_kept regs regs'.
Proof.
  intros regs regs' AG r Hcs. apply AG. intros Hin. unfold sl_clob in Hin. cbn [In] in Hin. unfold callee_saved in Hcs.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; try contradiction; subst r;
  first [ (apply (f_equal bv_unsigned) in Hcs; vm_compute in Hcs; discriminate Hcs)
        | (apply (f_equal bv_unsigned) in Hin; vm_compute in Hin; discriminate Hin)
        | (vm_compute in Hcs; destruct Hcs as [Hc1 Hc2]; first [exact (Hc1 eq_refl) | exact (Hc2 eq_refl)]) ].
Qed.
Lemma mseqt_ms_cs : forall regs regs' : bvmap 5 word, regs_agree (fun r => In r memset_clob) regs regs' -> cs_kept regs regs'.
Proof.
  intros regs regs' AG r Hcs. apply AG. intros Hin. unfold callee_saved in Hcs.
  repeat (hnf in Hin; destruct Hin as [Hin|Hin];
          [ subst r; destruct Hcs as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]];
            first [ (apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc)
                  | (vm_compute in Hc; destruct Hc as [Hc1 Hc2]; first [exact (Hc1 eq_refl) | exact (Hc2 eq_refl)]) ] | ]).
  all: exact Hin.
Qed.
Ltac mseqt_sc :=
  repeat match goal with |- context [alu64 ALU_SLTU (Z_to_bv 64 ?p) (Z_to_bv 64 ?q)] => rewrite (mseqt_sltu_ge p q) by lia end;
  v23_and0; lazymatch goal with |- ?G => is_closed_term G end; vm_compute; reflexivity.
#[local] Ltac exB_sc_hook ::= first [ mcs_sc_hook | v23_sc_hook | mseqt_sc ].
Ltac td_isbr ST :=
  lazymatch type of ST with
  | ex_st ?segs _ _ _ _ _ ?pc _ _ =>
      let d := eval vm_compute in (match fetch_word segs (Z_to_bv 64 pc) with Some w => decode_any w | None => None end) in
      lazymatch d with Some (Branch _ _ _ _, _) => idtac | _ => fail end
  end.
Ltac td_loop rounds fuel stops fdef HK ST FZ :=
  tryif exb_at_stop stops ST then idtac else
  tryif exb_at_jalr ST then idtac else
  tryif td_isbr ST then
    (tryif assert_succeeds (exb_autoS 1%nat 1%nat stops (SCR [false] [] []) HK ST ltac:(fun _ => idtac))
     then exb_autoS rounds fuel stops (SCR [false] [] []) HK ST ltac:(fun _ => td_loop rounds fuel stops fdef HK ST FZ)
     else exb_autoS rounds fuel stops (SCR [true] [] []) HK ST ltac:(fun _ => td_loop rounds fuel stops fdef HK ST FZ))
  else (exb_fstep fdef HK ST FZ; exb_norm ST; exb_autoS rounds fuel stops (SCR [] [] []) HK ST ltac:(fun _ => td_loop rounds fuel stops fdef HK ST FZ)).
Ltac td_drive rounds fuel stops fdef HK ST FZ :=
  exb_autoS rounds fuel stops (SCR [] [] []) HK ST ltac:(fun _ => td_loop rounds fuel stops fdef HK ST FZ).

Definition STOPS2 : list Z := [1107680; 1107992; 453468; 1174112; 1173204; 673912]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition MSEQT_WIN : Z := 4816.
Definition PC_PIXCOPY : word := 453468%bv.
Lemma PC_PIXCOPY_eq : Z_to_bv 64 453468 = PC_PIXCOPY.
Proof. apply bv_eq; reflexivity. Qed.
Definition PC_CSC : word := 673912%bv.
Lemma PC_CSC_eq : Z_to_bv 64 673912 = PC_CSC.
Proof. apply bv_eq; reflexivity. Qed.
(* [comment removed for export] *)
Definition RK_mseqt : Z := RK_pixcopy + 2 + RK_csc 8 + RK_csc 1.
Definition RB_mseqt (w h cm : Z) : Z := (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) + 2 * 2 ^ 17 + RB_csc 8 w h 1 + RB_csc 1 w h 1.

Section Tail.
Hypothesis HCSC : csc_contract_t.

Lemma mseq_tail : forall (fx : FPState) C Ar A m md regs (regsE : bvmap 5 word) (s pixs w h cm datas sa arr s1 s2 : Z) (cv : cmapv) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> MBC C -> W C A m md -> sub_live Ar A ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + MSEQT_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = Z_to_bv 64 681724 -> getr regs 2 = Z_to_bv 64 (s + -448) -> getr regs 3 = getr regsE 3 -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 pixs -> getr regs 8 = Z_to_bv 64 0 -> getr regs 9 = Z_to_bv 64 98147 ->
  getr regs 18 = Z_to_bv 64 2 -> getr regs 19 = Z_to_bv 64 pixs -> getr regs 20 = Z_to_bv 64 sa ->
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
  rdn SEGS m (Z_to_bv 64 (sa + 0)) 4 = Some (Z_to_le_bytes 4 50) ->
  rdn SEGS m (Z_to_bv 64 (sa + 4)) 4 = Some (Z_to_le_bytes 4 2) ->
  rdn SEGS m (Z_to_bv 64 (sa + 8)) 4 = Some (Z_to_le_bytes 4 1) ->
  rdn SEGS m (Z_to_bv 64 (sa + 16)) 8 = Some (Z_to_le_bytes 8 arr) ->
  rdn SEGS m (Z_to_bv 64 (arr + 0)) 8 = Some (Z_to_le_bytes 8 s1) ->
  rdn SEGS m (Z_to_bv 64 (arr + 8)) 8 = Some (Z_to_le_bytes 8 s2) ->
  rdn SEGS m (Z_to_bv 64 (s1 + 0)) 1 = Some (Z_to_le_bytes 1 99) ->
  rdn SEGS m (Z_to_bv 64 (s1 + 1)) 1 = Some (Z_to_le_bytes 1 49) ->
  rdn SEGS m (Z_to_bv 64 (s1 + 2)) 1 = Some (Z_to_le_bytes 1 46) ->
  rdn SEGS m (Z_to_bv 64 (s1 + 3)) 1 = Some (Z_to_le_bytes 1 56) ->
  rdn SEGS m (Z_to_bv 64 (s1 + 4)) 1 = Some (Z_to_le_bytes 1 32) ->
  rdn SEGS m (Z_to_bv 64 (s1 + 5)) 1 = Some (Z_to_le_bytes 1 0) ->
  rdn SEGS m (Z_to_bv 64 (s2 + 0)) 1 = Some (Z_to_le_bytes 1 32) ->
  rdn SEGS m (Z_to_bv 64 (s2 + 1)) 1 = Some (Z_to_le_bytes 1 99) ->
  rdn SEGS m (Z_to_bv 64 (s2 + 2)) 1 = Some (Z_to_le_bytes 1 51) ->
  rdn SEGS m (Z_to_bv 64 (s2 + 3)) 1 = Some (Z_to_le_bytes 1 48) ->
  rdn SEGS m (Z_to_bv 64 (s2 + 4)) 1 = Some (Z_to_le_bytes 1 46) ->
  rdn SEGS m (Z_to_bv 64 (s2 + 5)) 1 = Some (Z_to_le_bytes 1 49) ->
  rdn SEGS m (Z_to_bv 64 (s2 + 6)) 1 = Some (Z_to_le_bytes 1 0) ->
  rdn SEGS m (Z_to_bv 64 (s + -424)) 8 = Some (Z_to_le_bytes 8 sa) ->
  rdn SEGS m (Z_to_bv 64 (s + -416)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s + -376)) 4 = Some (Z_to_le_bytes 4 0) ->
  getr regsE 1 = ret -> ret_ok ret -> getr regsE 2 = Z_to_bv 64 s -> getr regsE 4 = Z_to_bv 64 1278416 ->
  PIXat m pixs (O23LeptPixCopyT.hdv w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  live A (Z_to_bv 64 sa) = Some 24%Z -> live Ar (Z_to_bv 64 sa) = None -> live (c_A0 C) (Z_to_bv 64 sa) = None -> (0 <= sa < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 arr) = Some 400%Z -> live Ar (Z_to_bv 64 arr) = None -> live (c_A0 C) (Z_to_bv 64 arr) = None -> (0 <= arr < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 s1) = Some 6%Z -> live Ar (Z_to_bv 64 s1) = None -> live (c_A0 C) (Z_to_bv 64 s1) = None -> (0 <= s1 < 2 ^ 64)%Z ->
  live A (Z_to_bv 64 s2) = Some 7%Z -> live Ar (Z_to_bv 64 s2) = None -> live (c_A0 C) (Z_to_bv 64 s2) = None -> (0 <= s2 < 2 ^ 64)%Z ->
  Z_to_bv 64 sa <> Z_to_bv 64 arr ->
  Z_to_bv 64 sa <> Z_to_bv 64 s1 ->
  Z_to_bv 64 arr <> Z_to_bv 64 s1 ->
  Z_to_bv 64 sa <> Z_to_bv 64 s2 ->
  Z_to_bv 64 arr <> Z_to_bv 64 s2 ->
  Z_to_bv 64 s1 <> Z_to_bv 64 s2 ->
  (forall q : word, ~ In q [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] -> live A q = live Ar q) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_mseqt <= kR)%Z -> (RB_mseqt w h cm <= bR)%Z ->
  (forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (pixd cd data : Z) (cv' : cmapv),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get (@fp_regs fx) r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regsE regs' -> getr regs' 10 = Z_to_bv 64 pixd ->
     sub_live Ar A' -> POSTM C Ar s m m' ->
     pix1_at C A A' m' pixd w h cd data cv' -> (pixd <> data)%Z -> p1_rest Ar A' pixd data cd cv' [] ->
     aroom A' vm' (kR - RK_mseqt) (bR - RB_mseqt w h cm) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 453468) m al_rom) md) S.
Proof.
  intros fx C Ar A0 m0 md r0 regsE s pixs w h cm datas sa arr s1 s2 cv ret S FZ CK MB HW0 SUBr Hs16 Hlo Hhi
         H1 H2 H3 H4 H10 H11 H8 H9 H18 H19 H20 SV1 SV8 SV9 SV18 SV19 SV20 SV21 SV22 SV23 SV24 SV25 SV26 SV27
         Ksa0 Ksa4 Ksa8 Ksa16 Karr0 Karr8 Ks1_0 Ks1_1 Ks1_2 Ks1_3 Ks1_4 Ks1_5 Ks2_0 Ks2_1 Ks2_2 Ks2_3 Ks2_4 Ks2_5 Ks2_6
         Kf424 Kf416 Kf376 HE1 Hret HE2 HE4 PXs HOK Hw1 Hh1 Lpixs_a0 Ldatas_a0 HCM
         Lsa_a0 Fsa F0sa RRsa Larr_a0 Farr F0arr RRarr Ls1_a0 Fs1 F0s1 RRs1 Ls2_a0 Fs2 F0s2 RRs2
         NE_sa_arr NE_sa_s1 NE_arr_s1 NE_sa_s2 NE_arr_s2 NE_s1_s2 LDEL0 kR bR RM0 HkR HbR HC.
  unfold MSEQT_WIN in *.
  assert (HRA : ex_keep (Z_to_bv 64 (bv_unsigned (getr regsE ex_rg1)) = ret)) by (unfold ex_keep; rewrite zbv_self; exact HE1).
  assert (HG3 : ex_keep (getr r0 ex_r3 = getr regsE ex_r3)) by exact H3.
  assert (HE2k : ex_keep (getr regsE ex_r2 = Z_to_bv 64 s)) by exact HE2.
  assert (HE4k : ex_keep (getr regsE ex_r4 = Z_to_bv 64 1278416)) by exact HE4.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C Ar s m0) as PM0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 4816)%Z) by lia.
  assert (GLO2 : (s - 4816 + Z.of_nat (Z.to_nat 4816) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (4816 <= s)%Z) by lia.
  pose proof (mcs_al16 C A0 m0 _ sa 24 HW0 Lsa_a0 RRsa) as ALsa.
  destruct (exW_blk_rng C A0 m0 _ sa 24 CK HW0 Lsa_a0 RRsa ltac:(lia)) as (Gsa1 & Gsa2 & Gsa3).
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 4816 sa 24 CK HW0 Lsa_a0 eq_refl RRsa GLO1) as WAPsa.
  pose proof (exW_blk_img_apart_h2 C A0 m0 _ sa 24 CK HW0 Lsa_a0 RRsa eq_refl eq_refl) as IMGAPsa. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPsa.
  pose proof (mcs_kn_blk SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) (EVar 35) (EVar 32) sa 24 s 4816 65536 1347584 p16_segs CK HW0 Lsa_a0 RRsa eq_refl eq_refl eq_refl RS ALsa WAPsa IMGAPsa) as HKb_sa.
  pose proof (mcs_al16 C A0 m0 _ arr 400 HW0 Larr_a0 RRarr) as ALarr.
  destruct (exW_blk_rng C A0 m0 _ arr 400 CK HW0 Larr_a0 RRarr ltac:(lia)) as (Garr1 & Garr2 & Garr3).
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 4816 arr 400 CK HW0 Larr_a0 eq_refl RRarr GLO1) as WAParr.
  pose proof (exW_blk_img_apart_h2 C A0 m0 _ arr 400 CK HW0 Larr_a0 RRarr eq_refl eq_refl) as IMGAParr. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAParr.
  pose proof (mcs_kn_blk SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) (EVar 36) (EVar 32) arr 400 s 4816 65536 1347584 p16_segs CK HW0 Larr_a0 RRarr eq_refl eq_refl eq_refl RS ALarr WAParr IMGAParr) as HKb_arr.
  pose proof (mcs_al16 C A0 m0 _ s1 6 HW0 Ls1_a0 RRs1) as ALs1.
  destruct (exW_blk_rng C A0 m0 _ s1 6 CK HW0 Ls1_a0 RRs1 ltac:(lia)) as (Gs11 & Gs12 & Gs13).
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 4816 s1 6 CK HW0 Ls1_a0 eq_refl RRs1 GLO1) as WAPs1.
  pose proof (exW_blk_img_apart_h2 C A0 m0 _ s1 6 CK HW0 Ls1_a0 RRs1 eq_refl eq_refl) as IMGAPs1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPs1.
  pose proof (mcs_kn_blk SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) (EVar 37) (EVar 32) s1 6 s 4816 65536 1347584 p16_segs CK HW0 Ls1_a0 RRs1 eq_refl eq_refl eq_refl RS ALs1 WAPs1 IMGAPs1) as HKb_s1.
  pose proof (mcs_al16 C A0 m0 _ s2 7 HW0 Ls2_a0 RRs2) as ALs2.
  destruct (exW_blk_rng C A0 m0 _ s2 7 CK HW0 Ls2_a0 RRs2 ltac:(lia)) as (Gs21 & Gs22 & Gs23).
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 4816 s2 7 CK HW0 Ls2_a0 eq_refl RRs2 GLO1) as WAPs2.
  pose proof (exW_blk_img_apart_h2 C A0 m0 _ s2 7 CK HW0 Ls2_a0 RRs2 eq_refl eq_refl) as IMGAPs2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPs2.
  pose proof (mcs_kn_blk SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) (EVar 38) (EVar 32) s2 7 s 4816 65536 1347584 p16_segs CK HW0 Ls2_a0 RRs2 eq_refl eq_refl eq_refl RS ALs2 WAPs2 IMGAPs2) as HKb_s2.
  pose proof (exW_blk_apart_h C A0 m0 _ sa arr 24 400 CK HW0 Lsa_a0 Larr_a0 NE_sa_arr RRsa RRarr ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_arr.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0) _ _ (ex_kdisj_apart SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0 (EVar 35) (EVar 36) sa arr 0 24 0 400 eq_refl eq_refl RRsa RRarr AP_sa_arr) (@Forall_nil kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0))) as HKd_sa_arr.
  pose proof (exW_blk_apart_h C A0 m0 _ sa s1 24 6 CK HW0 Lsa_a0 Ls1_a0 NE_sa_s1 RRsa RRs1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_s1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0) _ _ (ex_kdisj_apart SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0 (EVar 35) (EVar 37) sa s1 0 24 0 6 eq_refl eq_refl RRsa RRs1 AP_sa_s1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0))) as HKd_sa_s1.
  pose proof (exW_blk_apart_h C A0 m0 _ arr s1 400 6 CK HW0 Larr_a0 Ls1_a0 NE_arr_s1 RRarr RRs1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_s1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0) _ _ (ex_kdisj_apart SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0 (EVar 36) (EVar 37) arr s1 0 400 0 6 eq_refl eq_refl RRarr RRs1 AP_arr_s1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0))) as HKd_arr_s1.
  pose proof (exW_blk_apart_h C A0 m0 _ sa s2 24 7 CK HW0 Lsa_a0 Ls2_a0 NE_sa_s2 RRsa RRs2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0) _ _ (ex_kdisj_apart SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0 (EVar 35) (EVar 38) sa s2 0 24 0 7 eq_refl eq_refl RRsa RRs2 AP_sa_s2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0))) as HKd_sa_s2.
  pose proof (exW_blk_apart_h C A0 m0 _ arr s2 400 7 CK HW0 Larr_a0 Ls2_a0 NE_arr_s2 RRarr RRs2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0) _ _ (ex_kdisj_apart SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0 (EVar 36) (EVar 38) arr s2 0 400 0 7 eq_refl eq_refl RRarr RRs2 AP_arr_s2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0))) as HKd_arr_s2.
  pose proof (exW_blk_apart_h C A0 m0 _ s1 s2 6 7 CK HW0 Ls1_a0 Ls2_a0 NE_s1_s2 RRs1 RRs2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s1_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0) _ _ (ex_kdisj_apart SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0 (EVar 37) (EVar 38) s1 s2 0 6 0 7 eq_refl eq_refl RRs1 RRs2 AP_s1_s2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0))) as HKd_s1_s2.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) m0 [KRange (EVar 32) 1422624 (2 ^ 63); KAlign (EVar 32) 16; KWord (SA (EVar 32) (-8)) 8 (EVar 39); KWord (SA (EVar 32) (-16)) 8 (EVar 40); KWord (SA (EVar 32) (-24)) 8 (EVar 41); KWord (SA (EVar 32) (-32)) 8 (EVar 42); KWord (SA (EVar 32) (-40)) 8 (EVar 43); KWord (SA (EVar 32) (-48)) 8 (EVar 44); KWord (SA (EVar 32) (-56)) 8 (EVar 45); KWord (SA (EVar 32) (-64)) 8 (EVar 46); KWord (SA (EVar 32) (-72)) 8 (EVar 47); KWord (SA (EVar 32) (-80)) 8 (EVar 48); KWord (SA (EVar 32) (-88)) 8 (EVar 49); KWord (SA (EVar 32) (-96)) 8 (EVar 50); KWord (SA (EVar 32) (-104)) 8 (EVar 51); KWord (SA (EVar 32) (-424)) 8 (EVar 35); KWord (SA (EVar 32) (-416)) 8 (ELit 0); KWord (SA (EVar 32) (-376)) 4 (ELit 0); KWord (SA (EVar 35) 0) 4 (ELit 50); KWord (SA (EVar 35) 4) 4 (ELit 2); KWord (SA (EVar 35) 8) 4 (ELit 1); KWord (SA (EVar 35) 16) 8 (EVar 36); KWord (SA (EVar 36) 0) 8 (EVar 37); KWord (SA (EVar 36) 8) 8 (EVar 38); KWord (SA (EVar 37) 0) 1 (ELit 99); KWord (SA (EVar 37) 1) 1 (ELit 49); KWord (SA (EVar 37) 2) 1 (ELit 46); KWord (SA (EVar 37) 3) 1 (ELit 56); KWord (SA (EVar 37) 4) 1 (ELit 32); KWord (SA (EVar 37) 5) 1 (ELit 0); KWord (SA (EVar 38) 0) 1 (ELit 32); KWord (SA (EVar 38) 1) 1 (ELit 99); KWord (SA (EVar 38) 2) 1 (ELit 51); KWord (SA (EVar 38) 3) 1 (ELit 48); KWord (SA (EVar 38) 4) 1 (ELit 46); KWord (SA (EVar 38) 5) 1 (ELit 49); KWord (SA (EVar 38) 6) 1 (ELit 0)]).
  { unfold know_ok.
    apply Forall_cons; [ex_know1 r0|].
    apply Forall_cons; [ex_know1 r0|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV1]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV8]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV9]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV18]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV19]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV20]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV21]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV22]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV23]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV24]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV25]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV26]|].
    apply Forall_cons; [eapply ex_kword_w; [reflexivity | apply WalksLib.zbv_self | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | exact SV27]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Kf424]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Kf416]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Kf376]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ksa0]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ksa4]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ksa8]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ksa16]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Karr0]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Karr8]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks1_0]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks1_1]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks1_2]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks1_3]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks1_4]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks1_5]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks2_0]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks2_1]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks2_2]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks2_3]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks2_4]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks2_5]|].
    apply Forall_cons; [eapply ex_kword_Z; [reflexivity | reflexivity | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia | exact Ks2_6]|].
    apply Forall_nil. }
  pose proof (W_sok_win C A0 m0 _ (s - 4816) (Z.to_nat 4816) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 1410112 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0]) (EVar 52) (EVar 32) (exW_canary SEGS 1410112 m0) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKb_sa (proj2 (Forall_app _ _ _) (conj HKb_arr (proj2 (Forall_app _ _ _) (conj HKb_s1 (proj2 (Forall_app _ _ _) (conj HKb_s2 (proj2 (Forall_app _ _ _) (conj HKd_sa_arr (proj2 (Forall_app _ _ _) (conj HKd_sa_s1 (proj2 (Forall_app _ _ _) (conj HKd_arr_s1 (proj2 (Forall_app _ _ _) (conj HKd_sa_s2 (proj2 (Forall_app _ _ _) (conj HKd_arr_s2 (proj2 (Forall_app _ _ _) (conj HKd_s1_s2 HKf0)))))))))))))))))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; sa; arr; s1; s2; bv_unsigned (getr regsE ex_rg1); bv_unsigned (getr regsE ex_rg8); bv_unsigned (getr regsE ex_rg9); bv_unsigned (getr regsE ex_rg18); bv_unsigned (getr regsE ex_rg19); bv_unsigned (getr regsE ex_rg20); bv_unsigned (getr regsE ex_rg21); bv_unsigned (getr regsE ex_rg22); bv_unsigned (getr regsE ex_rg23); bv_unsigned (getr regsE ex_rg24); bv_unsigned (getr regsE ex_rg25); bv_unsigned (getr regsE ex_rg26); bv_unsigned (getr regsE ex_rg27); exW_canary SEGS 1410112 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKb_sa HKb_arr HKb_s1 HKb_s2 HKd_sa_arr HKd_sa_s1 HKd_arr_s1 HKd_sa_s2 HKd_arr_s2 HKd_s1_s2 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C Ar s m0 M0).
  { subst M0. apply (exW_win_blks C A0 Ar m0 _ E0 log0 (EVar 32) s 4816 [] CK HW0 SUBr Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  assert (PXsM0 : PIXat M0 pixs (O23LeptPixCopyT.hdv w h 1 cm datas)).
  { subst M0. exact (mcs_pix_blks C A0 m0 _ E0 log0 (EVar 32) s 4816 pixs [] _ CK HW0 GLO1 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS (Forall_nil _) Lpixs_a0 PXs). }
  assert (HCMM0 : cm = 0%Z \/ (CMAPat M0 cm cv /\ cmap_ok cv /\ live A0 (Z_to_bv 64 cm) = Some 24%Z /\ live A0 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
  { destruct HCM as [X | (X1 & X2 & X3 & X4)]; [left; exact X | right; refine (conj _ (conj X2 (conj X3 X4)))].
    subst M0. exact (mcs_cmap_blks C A0 m0 _ E0 log0 (EVar 32) s 4816 cm [] _ CK HW0 GLO1 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS (Forall_nil _) X3 X1). }
  assert (RKc8 : (0 <= RK_csc 8)%Z) by exW_cmp. assert (RKc1 : (0 <= RK_csc 1)%Z) by exW_cmp.
  pose proof (RB_csc_nonneg 8 w h 1) as RBc8. pose proof (RB_csc_nonneg 1 w h 1) as RBc1.
  rewrite PC_PIXCOPY_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopy_sureT_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) pixs w h 1 cm datas cv (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0
             PXsM0 HOK Hw1 Hh1 Lpixs_a0 Ldatas_a0 HCMM0 kR bR ltac:(rewrite with_vmmaps_vmmaps; exact RM0)
             ltac:(clear - HkR RKc8 RKc1; unfold RK_mseqt in HkR; lia) ltac:(clear - HbR RBc8 RBc1; unfold RB_mseqt in HbR; lia)) end end.
  intros A1 m1 vm1 r1 HW1 CSx0 PMc0 [pixd [cd [data [A10_0 PTN]]]] RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  pose proof PTN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdata & NEpd & Fpixdx & Fdatax & F0pixd & F0data & Lpixd_a1 & Ldata_a1 & PXd1 & CMR1).
  assert (Rn1 : (0 <= 4 * (wpl_of w 1 * h))%Z) by (unfold wpl_of; apply Z.mul_nonneg_nonneg; [lia | apply Z.mul_nonneg_nonneg; [apply Z.div_pos; lia | lia]]).
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdata : (0 <= data < 2 ^ 64)%Z) by lia.
  destruct (p1_of_pixt' C A0 A1 m1 pixd w h cd data cv PTN) as (cv1 & P1_1 & PLV1).
  pose proof (p1_rest_new Ar A0 A1 pixd data cd cv1 _ LDEL0 PLV1) as PR1. clear PLV1 LDEL0.
  pose proof (pixt_sub C A0 A1 m1 pixd w h cd data cv PTN) as SUBa1.
  pose proof (sub_live_trans Ar A0 A1 SUBr SUBa1) as SUB1.
  assert (PM1 : POSTM C Ar s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_sub C Ar A0 _ _ _ SUBr). apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (SUBa1 _ _ Lsa_a0) as Lsa_a1.
  pose proof (SUBa1 _ _ Larr_a0) as Larr_a1.
  pose proof (SUBa1 _ _ Ls1_a0) as Ls1_a1.
  pose proof (SUBa1 _ _ Ls2_a0) as Ls2_a1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 35, 0%Z, 24%Z); (EVar 36, 0%Z, 400%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 4816 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A0 A0 M0 _ M0 m1 E0 (EVar 35) sa 24 CK HWs0 Lsa_a0 RRsa eq_refl (proj2 PMc0) Lsa_a0 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A0 A0 M0 _ M0 m1 E0 (EVar 36) arr 400 CK HWs0 Larr_a0 RRarr eq_refl (proj2 PMc0) Larr_a0 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A0 A0 M0 _ M0 m1 E0 (EVar 37) s1 6 CK HWs0 Ls1_a0 RRs1 eq_refl (proj2 PMc0) Ls1_a0 eq_refl)|].
    constructor; [exact (exW_kept_blk2 C A0 A0 M0 _ M0 m1 E0 (EVar 38) s2 7 CK HWs0 Ls2_a0 RRs2 eq_refl (proj2 PMc0) Ls2_a0 eq_refl)|].
    constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 53%nat E0 (ex_envL vals0 r1 [pixd; exW_canary SEGS 1410112 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixd; exW_canary SEGS 1410112 m1] 53%nat ltac:(vm_cast_no_check (eq_refl 53%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixd; exW_canary SEGS 1410112 m1]) m1 _) by (exact (know_ok_agree SEGS 53%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  try rewrite (fr_denot_agree 53%nat E0 (ex_envL vals0 r1 [pixd; exW_canary SEGS 1410112 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 85) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q1_0 Q2_0 Q4_0 PM0 HW0 PMc0 CS0 OFF0 RM0 A10_0 PXsM0 HCMM0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  assert (HKp1 : know_ok SEGS (ex_envL vals0 r1 [pixd; exW_canary SEGS 1410112 m1]) m1 [KRange (EVar 85) 4096 (2 ^ 64 - 65); KAlign (EVar 85) 16]).
  { unfold know_ok. apply Forall_cons; [eapply ex_krange; [reflexivity | lia | lia]|]. apply Forall_cons; [eapply ex_kalign; [reflexivity | lia | lia | exact ALpixd]|]. apply Forall_nil. }
  pose proof (W_sok_win C A1 m1 _ (s - 4816) (Z.to_nat 4816) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 1410112 m1 (canary_any m1)) as CANOK1.
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; exW_canary SEGS 1410112 m1]) (EVar 86) (EVar 32) (exW_canary SEGS 1410112 m1) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  pose proof (mcs_canary_eq C A1 m1 _ CK HW1) as CEQ1.
  exb_open HR HK ST.
  clear HR HKp1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C Ar s m1 M1).
  { subst M1. apply (exW_win_blks C A1 Ar m1 _ E1 log1 (EVar 32) s 4816 [] CK HW1 SUB1 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP1 as [HWs1 PMs1].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose proof (p1_sess C A0 A1 m1 _ E1 log1 (EVar 32) s 4816 [] pixd w h cd data cv1 CK HW1 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_1) as P1s1.
  pose (BS1 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r1 Q1_1.
  exW_cellB HK Hlf r1 BS1 (EVar 37) s1 0%Z 1%nat Cs1_0_1.
  exW_cellB HK Hlf r1 BS1 (EVar 37) s1 1%Z 1%nat Cs1_1_1.
  exW_cellB HK Hlf r1 BS1 (EVar 37) s1 2%Z 1%nat Cs1_2_1.
  exW_cellB HK Hlf r1 BS1 (EVar 37) s1 3%Z 1%nat Cs1_3_1.
  exW_cellB HK Hlf r1 BS1 (EVar 37) s1 4%Z 1%nat Cs1_4_1.
  exW_cellB HK Hlf r1 BS1 (EVar 37) s1 5%Z 1%nat Cs1_5_1.
  clear BS1.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop5 fxk C A1 Ar M1 _ Rc1 s s1 6 99 49 46 56 32 (Z_to_bv 64 ra) S CK HWs1 Ls1_a1 RRs1 eq_refl eq_refl Cs1_0_1 Cs1_1_1 Cs1_2_1 Cs1_3_1 Cs1_4_1 Cs1_5_1 Q10_1 Q1_1 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r2 m2 HW2 PMc1 EQ1 A10_1 AG1.
  pose proof (mseqt_sl_cs _ _ AG1) as CS1. clear AG1.
  assert (PM2 : POSTM C Ar s m0 m2) by (eapply POSTM_trans; [exact PM1|]; eapply POSTM_trans; [exact PMs1 | exact PMc1]).
  pose proof (p1_eq C A0 A1 _ m2 pixd w h cd data cv1 P1s1 EQ1) as P1_2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, (-4816)%Z, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 85, 0%Z, 64%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { repeat (apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x _; exact (EQ1 x)|]). apply Forall_nil. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixd; exW_canary SEGS 1410112 m1]).
  pose proof (regs_ok_agree 87%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 1410112 m2] 87%nat ltac:(vm_cast_no_check (eq_refl 87%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) m2 _) by (exact (know_ok_agree SEGS 87%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  try rewrite (fr_denot_agree 87%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (ELit 5) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 HW1 Q10_1 Q1_1 PM1 PMc1 EQ1 CS1 A10_1 P1s1 P1_1 Cs1_0_1 Cs1_1_1 Cs1_2_1 Cs1_3_1 Cs1_4_1 Cs1_5_1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (W_sok_win C A1 m2 _ (s - 4816) (Z.to_nat 4816) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 1410112 m2 (canary_any m2)) as CANOK2.
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 1410112 m2]) (EVar 119) (EVar 32) (exW_canary SEGS 1410112 m2) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  pose proof (mcs_canary_eq C A1 m2 _ CK HW2) as CEQ2.
  exb_open HR HK ST.
  clear HR HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C Ar s m2 M2).
  { subst M2. apply (exW_win_blks C A1 Ar m2 _ E2 log2 (EVar 32) s 4816 [] CK HW2 SUB1 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP2 as [HWs2 PMs2].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose proof (p1_sess C A0 A1 m2 _ E2 log2 (EVar 32) s 4816 [] pixd w h cd data cv1 CK HW2 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_2) as P1s2.
  pose (BS2 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2. exW_regfactB BS2 HR ex_r4 Q4_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  pose proof (alloc_margin_small (6 * 1) ltac:(exW_cmp)) as MG2.
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_2 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
  lazymatch type of RM1 with aroom _ _ ?kk ?bb =>
    apply (W_calloc16_sure (fx := fxk) C A1 M2 _ Rc2 6 1 kk bb (Z_to_bv 64 ret) sp' S CK HWs2 Q10_2 Q11_2 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM1) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 ; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(rewrite MG2; clear - HbR RBc8 RBc1 ; unfold RB_mseqt in HbR; lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_2
             ltac:(red; apply bv_eq; reflexivity) Q4_2 Q2_2 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end end.
  intros A2 m3 vm2 r3 res2 HW3 Hres2 CSx2 Hnz2 Fx2 Lo2 F0op1 LEQ2 ZERO2 ALop1 TOP2 PMc2 RM2.
  pose proof CSx2 as CS2. clear CSx2.
  rewrite with_vmmaps_twice in HW3 |- *.
  assert (Eres2 : res2 = Z_to_bv 64 (u res2)) by (symmetry; apply zbv_self).
  pose proof (u64_range res2) as RRop1. set (op1 := u res2) in *. clearbody op1. rewrite Eres2 in Hres2, Fx2, Lo2, F0op1, LEQ2, ZERO2. clear Eres2.
  change (6 * 1)%Z with 6%Z in *.
  rewrite MG2 in RM2.
  pose proof (exW_blk_img_apart_h2 C A2 m3 _ op1 6 CK HW3 Lo2 RRop1 eq_refl eq_refl) as IMGAPop1. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPop1.
  pose proof (exW_win_blk_apart_h C A2 m3 _ s 4816 op1 6 CK HW3 Lo2 eq_refl RRop1 GLO1) as WAPop1.
  assert (Fop1 : live Ar (Z_to_bv 64 op1) = None).
  { destruct (live Ar (Z_to_bv 64 op1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB1 _ _ EE) as XX. first [discriminate Fx2 | (rewrite Fx2 in XX; discriminate XX)]. }
  pose proof Lo2 as Lop1_a2.
  assert (NMop1 : (6 mod 4 <> 0)%Z) by (intro XX; vm_compute in XX; discriminate XX).
  assert (FAop1 : live A0 (Z_to_bv 64 op1) = None).
  { destruct (live A0 (Z_to_bv 64 op1)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUBa1 _ _ EE) as XX. first [discriminate Fx2 | (rewrite Fx2 in XX; discriminate XX)]. }
  assert (SUBa2 : sub_live A0 A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op1) by (intros ->; rewrite FAop1 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUBa1 q kq Lq). }
  assert (SUB2 : sub_live Ar A2).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op1) by (intros ->; rewrite Fop1 in Lq; discriminate Lq). rewrite (LEQ2 q NEq). exact (SUB1 q kq Lq). }
  assert (NE_arr_op1 : Z_to_bv 64 arr <> Z_to_bv 64 op1) by (intros EE; pose proof Larr_a1 as XX; rewrite EE, Fx2 in XX; discriminate XX).
  assert (Larr_a2 : live A2 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ2 _ NE_arr_op1); exact Larr_a1).
  pose proof (exW_blk_apart_h C A2 m3 _ arr op1 400 6 CK HW3 Larr_a2 Lop1_a2 NE_arr_op1 RRarr RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_op1.
  assert (NE_pixd_op1 : Z_to_bv 64 pixd <> Z_to_bv 64 op1) by (intros EE; pose proof Lpixd_a1 as XX; rewrite EE, Fx2 in XX; discriminate XX).
  assert (Lpixd_a2 : live A2 (Z_to_bv 64 pixd) = Some 64%Z) by (rewrite (LEQ2 _ NE_pixd_op1); exact Lpixd_a1).
  pose proof (exW_blk_apart_h C A2 m3 _ pixd op1 64 6 CK HW3 Lpixd_a2 Lop1_a2 NE_pixd_op1 RRpixd RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_pixd_op1.
  assert (NE_s1_op1 : Z_to_bv 64 s1 <> Z_to_bv 64 op1) by (intros EE; pose proof Ls1_a1 as XX; rewrite EE, Fx2 in XX; discriminate XX).
  assert (Ls1_a2 : live A2 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ2 _ NE_s1_op1); exact Ls1_a1).
  pose proof (exW_blk_apart_h C A2 m3 _ s1 op1 6 6 CK HW3 Ls1_a2 Lop1_a2 NE_s1_op1 RRs1 RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s1_op1.
  assert (NE_s2_op1 : Z_to_bv 64 s2 <> Z_to_bv 64 op1) by (intros EE; pose proof Ls2_a1 as XX; rewrite EE, Fx2 in XX; discriminate XX).
  assert (Ls2_a2 : live A2 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ2 _ NE_s2_op1); exact Ls2_a1).
  pose proof (exW_blk_apart_h C A2 m3 _ s2 op1 7 6 CK HW3 Ls2_a2 Lop1_a2 NE_s2_op1 RRs2 RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s2_op1.
  assert (NE_sa_op1 : Z_to_bv 64 sa <> Z_to_bv 64 op1) by (intros EE; pose proof Lsa_a1 as XX; rewrite EE, Fx2 in XX; discriminate XX).
  assert (Lsa_a2 : live A2 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ2 _ NE_sa_op1); exact Lsa_a1).
  pose proof (exW_blk_apart_h C A2 m3 _ sa op1 24 6 CK HW3 Lsa_a2 Lop1_a2 NE_sa_op1 RRsa RRop1 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_op1.
  assert (PM3 : POSTM C Ar s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_sub C Ar A1 _ _ _ SUB1).
    apply (POSTM_mono C A1 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (p1_hop C A0 A1 A2 _ m3 pixd w h cd data cv1 (Z_to_bv 64 op1) P1s2 LEQ2 (or_introl Fx2) (or_introl (proj2 PMc2))) as P1_3.
  pose proof (p1_rest_add Ar A1 A2 pixd data cd cv1 _ (Z_to_bv 64 op1) PR1 LEQ2) as PR2.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 85, 0%Z, 64%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 4816 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M2 _ M2 m3 E2 (EVar 36) arr 400 CK HWs2 Larr_a1 RRarr eq_refl (proj2 PMc2) Larr_a1 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M2 _ M2 m3 E2 (EVar 85) pixd 64 CK HWs2 Lpixd_a1 RRpixd eq_refl (proj2 PMc2) Lpixd_a1 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M2 _ M2 m3 E2 (EVar 37) s1 6 CK HWs2 Ls1_a1 RRs1 eq_refl (proj2 PMc2) Ls1_a1 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M2 _ M2 m3 E2 (EVar 38) s2 7 CK HWs2 Ls2_a1 RRs2 eq_refl (proj2 PMc2) Ls2_a1 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A1 A1 M2 _ M2 m3 E2 (EVar 35) sa 24 CK HWs2 Lsa_a1 RRsa eq_refl (proj2 PMc2) Lsa_a1 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m2]).
  pose proof (regs_ok_agree 120%nat E2 (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [op1; exW_canary SEGS 1410112 m3] 120%nat ltac:(vm_cast_no_check (eq_refl 120%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3 _) by (exact (know_ok_agree SEGS 120%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  try rewrite (fr_denot_agree 120%nat E2 (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r3 ex_r10 (EVar 152) HRn3 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres2)) as HRx3. clear HRn3. rename HRx3 into HRn3.
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 HW2 Q10_2 Q11_2 Q1_2 Q2_2 Q4_2 PM2 PMc2 CS2 Hres2 P1s2 P1_2 PR1 MG2 TOP2 LEQ2 Hnz2 Fx2 Lo2 OFF2 RM1 SUB1 res2 Larr_a1 Lpixd_a1 Ls1_a1 Ls2_a1 Lsa_a1 SUBa1.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (W_sok_win C A2 m3 _ (s - 4816) (Z.to_nat 4816) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 1410112 m3 (canary_any m3)) as CANOK3.
  pose proof (exW_kn_fixed SEGS C A2 m3 _ (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) (EVar 153) (EVar 32) (exW_canary SEGS 1410112 m3) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (exW_kn_blk SEGS C A2 m3 _ (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) (EVar 152) (EVar 32) op1 6 s 4816 65536 1347584 p16_segs CK HW3 Lop1_a2 RRop1 eq_refl eq_refl eq_refl RS ALop1 ZERO2 WAPop1 IMGAPop1) as HKb3.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3 (EVar 36) (EVar 152) arr op1 0 400 0 6 eq_refl eq_refl RRarr RRop1 AP_arr_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3))) as HKd3_arr.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3 (EVar 85) (EVar 152) pixd op1 0 64 0 6 eq_refl eq_refl RRpixd RRop1 AP_pixd_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3))) as HKd3_pixd.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3 (EVar 37) (EVar 152) s1 op1 0 6 0 6 eq_refl eq_refl RRs1 RRop1 AP_s1_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3))) as HKd3_s1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3 (EVar 38) (EVar 152) s2 op1 0 7 0 6 eq_refl eq_refl RRs2 RRop1 AP_s2_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3))) as HKd3_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3) _ _ (ex_kdisj_apart SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3 (EVar 35) (EVar 152) sa op1 0 24 0 6 eq_refl eq_refl RRsa RRop1 AP_sa_op1) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals2 r3 [op1; exW_canary SEGS 1410112 m3]) m3))) as HKd3_sa.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb3 (proj2 (Forall_app _ _ _) (conj HKd3_arr (proj2 (Forall_app _ _ _) (conj HKd3_pixd (proj2 (Forall_app _ _ _) (conj HKd3_s1 (proj2 (Forall_app _ _ _) (conj HKd3_s2 (proj2 (Forall_app _ _ _) (conj HKd3_sa (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))))))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  pose proof (mcs_canary_eq C A2 m3 _ CK HW3) as CEQ3.
  exb_open HR HK ST.
  clear HR HKb3 HKd3_arr HKd3_pixd HKd3_s1 HKd3_s2 HKd3_sa HKf3 HKa3 SOK3 CANOK3 ZERO2 IMGAPop1 WAPop1 AP_arr_op1 AP_pixd_op1 AP_s1_op1 AP_s2_op1 AP_sa_op1.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C Ar s m3 M3).
  { subst M3. apply (exW_win_blks C A2 Ar m3 _ E3 log3 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] CK HW3 SUB2 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop1 (conj Lop1_a2 (conj Fop1 F0op1))))|].
    constructor. }
  destruct WP3 as [HWs3 PMs3].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  assert (PB3 : p1_blks_ok A0 A2 E3 [(EVar 152, op1, 6%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop1 (conj Lop1_a2 (or_intror (ex_intro _ 6%Z (conj Lop1_a2 NMop1)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A2 m3 _ E3 log3 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] pixd w h cd data cv1 CK HW3 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB3 P1_3) as P1s3.
  clear PB3.
  pose (BS3 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r1 Q1_3.
  exW_cellB HK Hlf r3 BS3 (EVar 37) s1 0%Z 1%nat Cs1_0_3.
  exW_cellB HK Hlf r3 BS3 (EVar 37) s1 1%Z 1%nat Cs1_1_3.
  exW_cellB HK Hlf r3 BS3 (EVar 37) s1 2%Z 1%nat Cs1_2_3.
  exW_cellB HK Hlf r3 BS3 (EVar 37) s1 3%Z 1%nat Cs1_3_3.
  exW_cellB HK Hlf r3 BS3 (EVar 37) s1 4%Z 1%nat Cs1_4_3.
  exW_cellB HK Hlf r3 BS3 (EVar 37) s1 5%Z 1%nat Cs1_5_3.
  clear BS3.
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop5 fxk C A2 Ar M3 _ Rc3 s s1 6 99 49 46 56 32 (Z_to_bv 64 ra) S CK HWs3 Ls1_a2 RRs1 eq_refl eq_refl Cs1_0_3 Cs1_1_3 Cs1_2_3 Cs1_3_3 Cs1_4_3 Cs1_5_3 Q10_3 Q1_3 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r4 m4 HW4 PMc3 EQ3 A10_3 AG3.
  pose proof (mseqt_sl_cs _ _ AG3) as CS3. clear AG3.
  assert (PM4 : POSTM C Ar s m0 m4) by (eapply POSTM_trans; [exact PM3|]; eapply POSTM_trans; [exact PMs3 | exact PMc3]).
  pose proof (p1_eq C A0 A2 _ m4 pixd w h cd data cv1 P1s3 EQ3) as P1_4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-4816)%Z, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 152, 0%Z, 6%Z); (EVar 85, 0%Z, 64%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { repeat (apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x _; exact (EQ3 x)|]). apply Forall_nil. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [op1; exW_canary SEGS 1410112 m3]).
  pose proof (regs_ok_agree 154%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 1410112 m4] 154%nat ltac:(vm_cast_no_check (eq_refl 154%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) m4 _) by (exact (know_ok_agree SEGS 154%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  try rewrite (fr_denot_agree 154%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (ELit 5) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 HW3 Q10_3 Q1_3 PM3 PMc3 EQ3 CS3 A10_3 P1s3 P1_3 Cs1_0_3 Cs1_1_3 Cs1_2_3 Cs1_3_3 Cs1_4_3 Cs1_5_3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (W_sok_win C A2 m4 _ (s - 4816) (Z.to_nat 4816) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 1410112 m4 (canary_any m4)) as CANOK4.
  pose proof (exW_kn_fixed SEGS C A2 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 1410112 m4]) (EVar 186) (EVar 32) (exW_canary SEGS 1410112 m4) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  pose proof (mcs_canary_eq C A2 m4 _ CK HW4) as CEQ4.
  exb_open HR HK ST.
  clear HR HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A2 M4 (with_vmmaps vm2 md) /\ POSTM C Ar s m4 M4).
  { subst M4. apply (exW_win_blks C A2 Ar m4 _ E4 log4 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] CK HW4 SUB2 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop1 (conj Lop1_a2 (conj Fop1 F0op1))))|].
    constructor. }
  destruct WP4 as [HWs4 PMs4].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  assert (PB4 : p1_blks_ok A0 A2 E4 [(EVar 152, op1, 6%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop1 (conj Lop1_a2 (or_intror (ex_intro _ 6%Z (conj Lop1_a2 NMop1)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A2 m4 _ E4 log4 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] pixd w h cd data cv1 CK HW4 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB4 P1_4) as P1s4.
  clear PB4.
  pose (BS4 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1)]).
  exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r11 Q11_4. exW_regfactB BS4 HR ex_r12 Q12_4. exW_regfactB BS4 HR ex_r1 Q1_4.
  clear BS4.
  lazymatch type of Q10_4 with _ = Z_to_bv 64 (s + ?off) => pose (DOFF4 := off) end.
  lazymatch type of Q12_4 with _ = Z_to_bv 64 ?nn => pose (DN4 := nn) end.
  lazymatch type of Q1_4 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (mcs_memset_hop (fx := fxk) C A2 A2 M4 _ Rc4 s (s + DOFF4) DN4 (Z_to_bv 64 ra) S CK HWs4 ltac:(intros q kq Lq; exact Lq) Hhi
             ltac:(unfold DOFF4; lia) ltac:(unfold DN4; lia) ltac:(unfold DOFF4, DN4; lia) Q1_4 ltac:(red; apply bv_eq; reflexivity) Q10_4 Q11_4 Q12_4) end end.
  intros r5 m5 HW5 PMc4 A10_4 AG4 OUT4 ZER4.
  pose proof (mseqt_ms_cs _ _ AG4) as CS4. clear AG4.
  assert (PM5 : POSTM C Ar s m0 m5) by (eapply POSTM_trans; [exact PM4|]; eapply POSTM_trans; [exact PMs4 | exact (POSTM_sub C Ar A2 _ _ _ SUB2 PMc4)]).
  pose proof (p1_same C A0 A2 _ m5 pixd w h cd data cv1 P1s4 (proj2 PMc4)) as P1_5.
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, (-4816)%Z, DOFF4); (EVar 32, (DOFF4 + DN4)%Z, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 152, 0%Z, 6%Z); (EVar 85, 0%Z, 64%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x Hx; apply OUT4; intros Hy; change (edenot E4 (EVar 32)) with (Z_to_bv 64 s) in Hx; rewrite u_Z2bv in Hx by lia; unfold DOFF4, DN4 in Hx, Hy; lia|]. apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x Hx; apply OUT4; intros Hy; change (edenot E4 (EVar 32)) with (Z_to_bv 64 s) in Hx; rewrite u_Z2bv in Hx by lia; unfold DOFF4, DN4 in Hx, Hy; lia|]. apply Forall_cons; [exact (mcs_kept_blk_win E4 M4 m5 (EVar 36) arr 400 s 4816 (s + DOFF4) (s + DOFF4 + DN4) OUT4 eq_refl RRarr (exW_win_blk_apart_h C A2 M4 _ s 4816 arr 400 CK HWs4 Larr_a2 eq_refl RRarr GLO1) ltac:(unfold DOFF4; lia) ltac:(unfold DOFF4, DN4; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E4 M4 m5 (EVar 152) op1 6 s 4816 (s + DOFF4) (s + DOFF4 + DN4) OUT4 eq_refl RRop1 (exW_win_blk_apart_h C A2 M4 _ s 4816 op1 6 CK HWs4 Lop1_a2 eq_refl RRop1 GLO1) ltac:(unfold DOFF4; lia) ltac:(unfold DOFF4, DN4; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E4 M4 m5 (EVar 85) pixd 64 s 4816 (s + DOFF4) (s + DOFF4 + DN4) OUT4 eq_refl RRpixd (exW_win_blk_apart_h C A2 M4 _ s 4816 pixd 64 CK HWs4 Lpixd_a2 eq_refl RRpixd GLO1) ltac:(unfold DOFF4; lia) ltac:(unfold DOFF4, DN4; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E4 M4 m5 (EVar 37) s1 6 s 4816 (s + DOFF4) (s + DOFF4 + DN4) OUT4 eq_refl RRs1 (exW_win_blk_apart_h C A2 M4 _ s 4816 s1 6 CK HWs4 Ls1_a2 eq_refl RRs1 GLO1) ltac:(unfold DOFF4; lia) ltac:(unfold DOFF4, DN4; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E4 M4 m5 (EVar 38) s2 7 s 4816 (s + DOFF4) (s + DOFF4 + DN4) OUT4 eq_refl RRs2 (exW_win_blk_apart_h C A2 M4 _ s 4816 s2 7 CK HWs4 Ls2_a2 eq_refl RRs2 GLO1) ltac:(unfold DOFF4; lia) ltac:(unfold DOFF4, DN4; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E4 M4 m5 (EVar 35) sa 24 s 4816 (s + DOFF4) (s + DOFF4 + DN4) OUT4 eq_refl RRsa (exW_win_blk_apart_h C A2 M4 _ s 4816 sa 24 CK HWs4 Lsa_a2 eq_refl RRsa GLO1) ltac:(unfold DOFF4; lia) ltac:(unfold DOFF4, DN4; lia))|]. apply Forall_nil. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m4]).
  pose proof (regs_ok_agree 187%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_call _ _ _ _ _ HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 1410112 m5] 187%nat ltac:(vm_cast_no_check (eq_refl 187%nat))) CS4) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) m5 _) by (exact (know_ok_agree SEGS 187%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  try rewrite (fr_denot_agree 187%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 HW4 Q10_4 Q11_4 Q12_4 Q1_4 PM4 PMc4 CS4 A10_4 OUT4 P1s4 P1_4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  pose proof (W_sok_win C A2 m5 _ (s - 4816) (Z.to_nat 4816) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 1410112 m5 (canary_any m5)) as CANOK5.
  pose proof (exW_kn_fixed SEGS C A2 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) (EVar 219) (EVar 32) (exW_canary SEGS 1410112 m5) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (mcs_kzero_win SEGS (ex_envL vals4 r5 [exW_canary SEGS 1410112 m5]) m5 (EVar 32) s DOFF4 DN4 eq_refl RS ltac:(unfold DOFF4; lia) eq_refl ltac:(unfold DOFF4, DN4; lia) ZER4) as HKz5.
  unfold DOFF4, DN4 in HKz5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKz5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  pose proof (mcs_canary_eq C A2 m5 _ CK HW5) as CEQ5.
  exb_open HR HK ST.
  clear HR HKz5 HKf5 HKa5 SOK5 CANOK5 ZER4 DOFF4 DN4.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A2 M5 (with_vmmaps vm2 md) /\ POSTM C Ar s m5 M5).
  { subst M5. apply (exW_win_blks C A2 Ar m5 _ E5 log5 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] CK HW5 SUB2 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop1 (conj Lop1_a2 (conj Fop1 F0op1))))|].
    constructor. }
  destruct WP5 as [HWs5 PMs5].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  assert (PB5 : p1_blks_ok A0 A2 E5 [(EVar 152, op1, 6%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop1 (conj Lop1_a2 (or_intror (ex_intro _ 6%Z (conj Lop1_a2 NMop1)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A2 m5 _ E5 log5 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] pixd w h cd data cv1 CK HW5 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB5 P1_5) as P1s5.
  clear PB5.
  pose (BS5 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r11 Q11_5. exW_regfactB BS5 HR ex_r12 Q12_5. exW_regfactB BS5 HR ex_r13 Q13_5.
  exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5. exW_regfactB BS5 HR ex_r4 Q4_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  pose proof (RB_csc_le1 8 w h cd) as RBl5.
  rewrite PC_CSC_eq.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_5 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst (mkFP ?frk ?csk) _ _ _ _) _) _ =>
  lazymatch type of RM2 with aroom _ _ ?kk ?bb =>
    apply (HCSC frk csk C A0 A2 M5 _ Rc5 sp' pixd 1%Z 8%Z w h cd data cv1 (Z_to_bv 64 ret) S CK MB HWs5 SUBa2 FZ Q2_5
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CSC_STACK; lia) ltac:(lia) Q1_5 ltac:(red; apply bv_eq; reflexivity) Q4_5 Q10_5 Q11_5 Q12_5 Q13_5 (or_introl (conj eq_refl eq_refl))
             P1s5 NEpd HOK Hw1 Hh1 kk bb ltac:(rewrite with_vmmaps_vmmaps; exact RM2) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5; unfold RK_mseqt, RB_mseqt in *; lia)) end end end end.
  intros fr5 cs5 A3 m6 vm3 r6 cm5 cv5 FZc5 FS5 HW6 CS5 A10_5 SUBa3 PMc5 P1c5 CL5 CKp5 RM3.
  rewrite with_vmmaps_twice in HW6 |- *.
  pose proof (sub_live_trans Ar A0 A3 SUBr SUBa3) as SUB3.
  assert (FSA5 : forall r : reg, In (u r) fs_list -> reg_get fr5 r = reg_get fr r) by (intros r Hr; rewrite (FS5 r Hr); reflexivity).
  assert (PM6 : POSTM C Ar s m0 m6).
  { eapply POSTM_trans; [exact PM5|]. eapply POSTM_trans; [exact PMs5|]. apply (POSTM_sub C Ar A0 _ _ _ SUBr).
    apply (POSTM_mono C A0 (s + OFF5) s); [unfold OFF5; lia | exact PMc5]. }
  pose proof (p1_rest_csc C Ar A0 A2 A3 _ pixd w h data cd cv1 cm5 cv5 _ PR2 P1s5 SUBr CL5) as PR3.
  pose proof (p1_csc_live C A0 A2 A3 _ pixd w h data cd cv1 cm5 cv5 (Z_to_bv 64 arr) 400 P1s5 CL5 CKp5 Larr_a2 (or_introl (ex_intro _ 400%Z Larr_a0))) as Larr_a3.
  pose proof (p1_csc_live C A0 A2 A3 _ pixd w h data cd cv1 cm5 cv5 (Z_to_bv 64 op1) 6 P1s5 CL5 CKp5 Lop1_a2 (or_intror (ex_intro _ 6%Z (conj Lop1_a2 NMop1)))) as Lop1_a3.
  pose proof (p1_csc_live C A0 A2 A3 _ pixd w h data cd cv1 cm5 cv5 (Z_to_bv 64 s1) 6 P1s5 CL5 CKp5 Ls1_a2 (or_introl (ex_intro _ 6%Z Ls1_a0))) as Ls1_a3.
  pose proof (p1_csc_live C A0 A2 A3 _ pixd w h data cd cv1 cm5 cv5 (Z_to_bv 64 s2) 7 P1s5 CL5 CKp5 Ls2_a2 (or_introl (ex_intro _ 7%Z Ls2_a0))) as Ls2_a3.
  pose proof (p1_csc_live C A0 A2 A3 _ pixd w h data cd cv1 cm5 cv5 (Z_to_bv 64 sa) 24 P1s5 CL5 CKp5 Lsa_a2 (or_introl (ex_intro _ 24%Z Lsa_a0))) as Lsa_a3.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, OFF5, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF5 4816 M5 m6 E5 (EVar 32) CK (proj1 PMc5) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A2 M5 _ M5 m6 E5 (EVar 36) arr 400 CK HWs5 Larr_a2 RRarr eq_refl (proj2 PMc5) Larr_a0 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A2 M5 _ M5 m6 E5 (EVar 37) s1 6 CK HWs5 Ls1_a2 RRs1 eq_refl (proj2 PMc5) Ls1_a0 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A2 M5 _ M5 m6 E5 (EVar 38) s2 7 CK HWs5 Ls2_a2 RRs2 eq_refl (proj2 PMc5) Ls2_a0 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A2 M5 _ M5 m6 E5 (EVar 35) sa 24 CK HWs5 Lsa_a2 RRsa eq_refl (proj2 PMc5) Lsa_a0 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m5]).
  pose proof (regs_ok_agree 220%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 1410112 m6] 220%nat ltac:(vm_cast_no_check (eq_refl 220%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) m6 _) by (exact (know_ok_agree SEGS 220%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  try rewrite (fr_denot_agree 220%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r6 ex_r10 (EVar 85) HRn6 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_5)) as HRx6. clear HRn6. rename HRx6 into HRn6.
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 HW5 Q10_5 Q11_5 Q12_5 Q13_5 Q1_5 Q2_5 Q4_5 PM5 PMc5 CS5 P1s5 P1_5 PR2 CL5 CKp5 OFF5 RM2 SUB2 FS5 FZ Larr_a2 Lop1_a2 Ls1_a2 Ls2_a2 Lsa_a2 SUBa2.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  pose proof (W_sok_win C A3 m6 _ (s - 4816) (Z.to_nat 4816) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 1410112 m6 (canary_any m6)) as CANOK6.
  pose proof (exW_kn_fixed SEGS C A3 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 1410112 m6]) (EVar 252) (EVar 32) (exW_canary SEGS 1410112 m6) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  pose proof (mcs_canary_eq C A3 m6 _ CK HW6) as CEQ6.
  rename FZc5 into FZ.
  rename P1c5 into P1_6.
  exb_open HR HK ST.
  clear HR HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc6 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A3 M6 (with_vmmaps vm3 md) /\ POSTM C Ar s m6 M6).
  { subst M6. apply (exW_win_blks C A3 Ar m6 _ E6 log6 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] CK HW6 SUB3 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop1 (conj Lop1_a3 (conj Fop1 F0op1))))|].
    constructor. }
  destruct WP6 as [HWs6 PMs6].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log6 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC6 : carry log6 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc6 : know_ok SEGS E6 M6 kn1) by (apply (carry_after SEGS E6 m6 log6 kn0 [] kn1 scs hs HC6 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  assert (PB6 : p1_blks_ok A0 A3 E6 [(EVar 152, op1, 6%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop1 (conj Lop1_a3 (or_intror (ex_intro _ 6%Z (conj Lop1_a3 NMop1)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A3 m6 _ E6 log6 (EVar 32) s 4816 [(EVar 152, op1, 6%Z)] pixd w h cm5 data cv5 CK HW6 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB6 P1_6) as P1s6.
  clear PB6.
  pose (BS6 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1)]).
  exW_regfactB BS6 HR ex_r10 Q10_6. exW_regfactB BS6 HR ex_r1 Q1_6. exW_regfactB BS6 HR ex_r2 Q2_6. exW_regfactB BS6 HR ex_r4 Q4_6.
  clear BS6.
  lazymatch type of Q2_6 with _ = Z_to_bv 64 (s + ?off) => pose (OFF6 := off) end.
  lazymatch type of Q1_6 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_6 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A3 M6 _ Rc6 (Z_to_bv 64 op1) (Z_to_bv 64 ret) 6 sp' S CK HWs6 Q10_6 Lop1_a3 F0op1 Q1_6
             ltac:(red; apply bv_eq; reflexivity) Q4_6 Q2_6 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A4 m7 vm4 r7 HW7 CSx6 Ldead6 LEQ6 PMc6 RTR6.
  pose proof CSx6 as CS6. clear CSx6.
  rewrite with_vmmaps_twice in HW7 |- *.
  assert (SUB4 : sub_live Ar A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op1) by (intros ->; rewrite Fop1 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUB3 q kq Lq). }
  assert (SUBa4 : sub_live A0 A4).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op1) by (intros ->; rewrite FAop1 in Lq; discriminate Lq). rewrite (LEQ6 q NEq). exact (SUBa3 q kq Lq). }
  assert (Larr_a4 : live A4 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ6 _ NE_arr_op1); exact Larr_a3).
  assert (Ls1_a4 : live A4 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ6 _ NE_s1_op1); exact Ls1_a3).
  assert (Ls2_a4 : live A4 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ6 _ NE_s2_op1); exact Ls2_a3).
  assert (Lsa_a4 : live A4 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ6 _ NE_sa_op1); exact Lsa_a3).
  assert (PM7 : POSTM C Ar s m0 m7).
  { eapply POSTM_trans; [exact PM6|]. eapply POSTM_trans; [exact PMs6|]. apply (POSTM_sub C Ar A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF6) s); [unfold OFF6; lia | exact PMc6]. }
  pose proof (RTR6 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM3) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5; unfold RK_mseqt, RB_mseqt in *; lia)) as RM4. rewrite !Z.sub_0_r in RM4.
  pose proof (p1_hop C A0 A3 A4 _ m7 pixd w h cm5 data cv5 (Z_to_bv 64 op1) P1s6 LEQ6 (or_intror (or_intror (ex_intro _ 6%Z (conj Lop1_a3 NMop1)))) (or_intror (proj2 PMc6))) as P1_7.
  pose proof (p1_rest_del Ar A3 A4 pixd data cm5 cv5 [Z_to_bv 64 op1; Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] (Z_to_bv 64 op1) PR3 LEQ6 Ldead6 Fop1 ltac:(intros q Hq; cbn [In] in Hq |- *; tauto)) as PR4.
  assert (KEPT6 : Forall (ex_region_kept E6 M6 m7) [(EVar 32, OFF6, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF6 4816 M6 m7 E6 (EVar 32) CK (proj1 PMc6) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 m7 _ M6 m7 E6 (EVar 36) arr 400 CK HW7 Larr_a4 RRarr eq_refl (proj2 PMc6) Larr_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 m7 _ M6 m7 E6 (EVar 37) s1 6 CK HW7 Ls1_a4 RRs1 eq_refl (proj2 PMc6) Ls1_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 m7 _ M6 m7 E6 (EVar 38) s2 7 CK HW7 Ls2_a4 RRs2 eq_refl (proj2 PMc6) Ls2_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 m7 _ M6 m7 E6 (EVar 35) sa 24 CK HW7 Lsa_a4 RRsa eq_refl (proj2 PMc6) Lsa_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E6 M6 m7 _ [] _ HKc6 KEPT6) as HKk6.
  match type of HKk6 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E6 m7 kk') in HKk6 end.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m6]).
  pose proof (regs_ok_agree 253%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa6.
  pose proof (exW_regs_call _ _ _ _ _ HRa6 (ex_regs_ok_junk vals6 r7 [exW_canary SEGS 1410112 m7] 253%nat ltac:(vm_cast_no_check (eq_refl 253%nat))) CS6) as HRn7.
  clear HRa6.
  assert (HKa7 : know_ok SEGS (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) m7 _) by (exact (know_ok_agree SEGS 253%nat E6 _ m7 _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk6)).
  try rewrite (fr_denot_agree 253%nat E6 (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) _ _ (vals_app_agree vals6 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc6 HKk6 KEPT6 HC6 HWs6 PMs6 HW6 Q10_6 Q1_6 Q2_6 Q4_6 PM6 PMc6 CS6 P1s6 P1_6 PR3 LEQ6 Ldead6 RTR6 OFF6 RM3 SUB3 Larr_a3 Ls1_a3 Ls2_a3 Lsa_a3 Lop1_a3 SUBa3.
  subst M6. clear log6. clear E6. try clear Rc6. clear KN6.
  lazymatch type of HRn7 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn7 end.
  pose proof (W_sok_win C A4 m7 _ (s - 4816) (Z.to_nat 4816) CK HW7 GLO1 GLO2) as SOK7.
  pose proof (exW_canary_ok SEGS 1410112 m7 (canary_any m7)) as CANOK7.
  pose proof (exW_kn_fixed SEGS C A4 m7 _ (ex_envL vals6 r7 [exW_canary SEGS 1410112 m7]) (EVar 285) (EVar 32) (exW_canary SEGS 1410112 m7) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW7 eq_refl (proj1 CANOK7) (proj2 CANOK7) eq_refl eq_refl eq_refl SOK7 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf7.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf7 HKa7)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn7 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN7 := kn) in HK end.
  pose proof (mcs_canary_eq C A4 m7 _ CK HW7) as CEQ7.
  exb_open HR HK ST.
  clear HR HKf7 HKa7 SOK7 CANOK7.
  repeat match goal with H : getr r7 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc7 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E7 := EEx) in HR, Hlf, HK, Hms |- *; set (log7 := LLx) in Hms, Hlf; set (M7 := mem_denot E7 m7 log7) in Hms end.
  assert (WP7 : W C A4 M7 (with_vmmaps vm4 md) /\ POSTM C Ar s m7 M7).
  { subst M7. apply (exW_win_blks C A4 Ar m7 _ E7 log7 (EVar 32) s 4816 [] CK HW7 SUB4 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP7 as [HWs7 PMs7].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log7 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC7 : carry log7 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc7 : know_ok SEGS E7 M7 kn1) by (apply (carry_after SEGS E7 m7 log7 kn0 [] kn1 scs hs HC7 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW7)) | exact (mp_lazy _ (w_pure _ _ _ _ HW7)) | exact Hms |].
  pose proof (p1_sess C A0 A4 m7 _ E7 log7 (EVar 32) s 4816 [] pixd w h cm5 data cv5 CK HW7 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_7) as P1s7.
  pose (BS7 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1)]).
  exW_regfactB BS7 HR ex_r10 Q10_7. exW_regfactB BS7 HR ex_r1 Q1_7.
  exW_cellB HK Hlf r7 BS7 (EVar 38) s2 0%Z 1%nat Cs2_0_7.
  exW_cellB HK Hlf r7 BS7 (EVar 38) s2 1%Z 1%nat Cs2_1_7.
  exW_cellB HK Hlf r7 BS7 (EVar 38) s2 2%Z 1%nat Cs2_2_7.
  exW_cellB HK Hlf r7 BS7 (EVar 38) s2 3%Z 1%nat Cs2_3_7.
  exW_cellB HK Hlf r7 BS7 (EVar 38) s2 4%Z 1%nat Cs2_4_7.
  exW_cellB HK Hlf r7 BS7 (EVar 38) s2 5%Z 1%nat Cs2_5_7.
  exW_cellB HK Hlf r7 BS7 (EVar 38) s2 6%Z 1%nat Cs2_6_7.
  clear BS7.
  lazymatch type of Q1_7 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop6 fxk C A4 Ar M7 _ Rc7 s s2 7 32 99 51 48 46 49 (Z_to_bv 64 ra) S CK HWs7 Ls2_a4 RRs2 eq_refl eq_refl Cs2_0_7 Cs2_1_7 Cs2_2_7 Cs2_3_7 Cs2_4_7 Cs2_5_7 Cs2_6_7 Q10_7 Q1_7 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r8 m8 HW8 PMc7 EQ7 A10_7 AG7.
  pose proof (mseqt_sl_cs _ _ AG7) as CS7. clear AG7.
  assert (PM8 : POSTM C Ar s m0 m8) by (eapply POSTM_trans; [exact PM7|]; eapply POSTM_trans; [exact PMs7 | exact PMc7]).
  pose proof (p1_eq C A0 A4 _ m8 pixd w h cm5 data cv5 P1s7 EQ7) as P1_8.
  assert (KEPT7 : Forall (ex_region_kept E7 M7 m8) [(EVar 32, (-4816)%Z, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { repeat (apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x _; exact (EQ7 x)|]). apply Forall_nil. }
  pose proof (ex_know_keepD SEGS E7 M7 m8 _ [] _ HKc7 KEPT7) as HKk7.
  match type of HKk7 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E7 m8 kk') in HKk7 end.
  pose (vals7 := vals6 ++ map (getr r7) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m7]).
  pose proof (regs_ok_agree 286%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa7.
  pose proof (exW_regs_call _ _ _ _ _ HRa7 (ex_regs_ok_junk vals7 r8 [exW_canary SEGS 1410112 m8] 286%nat ltac:(vm_cast_no_check (eq_refl 286%nat))) CS7) as HRn8.
  clear HRa7.
  assert (HKa8 : know_ok SEGS (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) m8 _) by (exact (know_ok_agree SEGS 286%nat E7 _ m8 _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk7)).
  try rewrite (fr_denot_agree 286%nat E7 (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) _ _ (vals_app_agree vals7 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r8 ex_r10 (ELit 6) HRn8 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_7)) as HRx8. clear HRn8. rename HRx8 into HRn8.
  clear HR HK Hlf Hms HKc7 HKk7 KEPT7 HC7 HWs7 PMs7 HW7 Q10_7 Q1_7 PM7 PMc7 EQ7 CS7 A10_7 P1s7 P1_7 Cs2_0_7 Cs2_1_7 Cs2_2_7 Cs2_3_7 Cs2_4_7 Cs2_5_7 Cs2_6_7.
  subst M7. clear log7. clear E7. try clear Rc7. clear KN7.
  lazymatch type of HRn8 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn8 end.
  pose proof (W_sok_win C A4 m8 _ (s - 4816) (Z.to_nat 4816) CK HW8 GLO1 GLO2) as SOK8.
  pose proof (exW_canary_ok SEGS 1410112 m8 (canary_any m8)) as CANOK8.
  pose proof (exW_kn_fixed SEGS C A4 m8 _ (ex_envL vals7 r8 [exW_canary SEGS 1410112 m8]) (EVar 318) (EVar 32) (exW_canary SEGS 1410112 m8) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW8 eq_refl (proj1 CANOK8) (proj2 CANOK8) eq_refl eq_refl eq_refl SOK8 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf8.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf8 HKa8)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn8 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN8 := kn) in HK end.
  pose proof (mcs_canary_eq C A4 m8 _ CK HW8) as CEQ8.
  exb_open HR HK ST.
  clear HR HKf8 HKa8 SOK8 CANOK8.
  repeat match goal with H : getr r8 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc8 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E8 := EEx) in HR, Hlf, HK, Hms |- *; set (log8 := LLx) in Hms, Hlf; set (M8 := mem_denot E8 m8 log8) in Hms end.
  assert (WP8 : W C A4 M8 (with_vmmaps vm4 md) /\ POSTM C Ar s m8 M8).
  { subst M8. apply (exW_win_blks C A4 Ar m8 _ E8 log8 (EVar 32) s 4816 [] CK HW8 SUB4 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP8 as [HWs8 PMs8].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log8 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC8 : carry log8 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc8 : know_ok SEGS E8 M8 kn1) by (apply (carry_after SEGS E8 m8 log8 kn0 [] kn1 scs hs HC8 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW8)) | exact (mp_lazy _ (w_pure _ _ _ _ HW8)) | exact Hms |].
  pose proof (p1_sess C A0 A4 m8 _ E8 log8 (EVar 32) s 4816 [] pixd w h cm5 data cv5 CK HW8 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_8) as P1s8.
  pose (BS8 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1)]).
  exW_regfactB BS8 HR ex_r10 Q10_8. exW_regfactB BS8 HR ex_r11 Q11_8. exW_regfactB BS8 HR ex_r1 Q1_8. exW_regfactB BS8 HR ex_r2 Q2_8. exW_regfactB BS8 HR ex_r4 Q4_8.
  clear BS8.
  lazymatch type of Q2_8 with _ = Z_to_bv 64 (s + ?off) => pose (OFF8 := off) end.
  pose proof (alloc_margin_small (7 * 1) ltac:(exW_cmp)) as MG8.
  lazymatch type of Q1_8 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_8 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
  lazymatch type of RM4 with aroom _ _ ?kk ?bb =>
    apply (W_calloc16_sure (fx := fxk) C A4 M8 _ Rc8 7 1 kk bb (Z_to_bv 64 ret) sp' S CK HWs8 Q10_8 Q11_8 ltac:(exW_cmp) ltac:(exW_cmp) ltac:(exW_cmp)
             ltac:(rewrite with_vmmaps_vmmaps; exact RM4) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(rewrite MG8; clear - HbR RBc8 RBc1 RBl5; unfold RB_mseqt in HbR; lia) ltac:(unfold ROOM_NMAX; exW_cmp) Q1_8
             ltac:(red; apply bv_eq; reflexivity) Q4_8 Q2_8 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)) end end end end.
  intros A5 m9 vm5 r9 res8 HW9 Hres8 CSx8 Hnz8 Fx8 Lo8 F0op2 LEQ8 ZERO8 ALop2 TOP8 PMc8 RM5.
  pose proof CSx8 as CS8. clear CSx8.
  rewrite with_vmmaps_twice in HW9 |- *.
  assert (Eres8 : res8 = Z_to_bv 64 (u res8)) by (symmetry; apply zbv_self).
  pose proof (u64_range res8) as RRop2. set (op2 := u res8) in *. clearbody op2. rewrite Eres8 in Hres8, Fx8, Lo8, F0op2, LEQ8, ZERO8. clear Eres8.
  change (7 * 1)%Z with 7%Z in *.
  rewrite MG8 in RM5.
  pose proof (exW_blk_img_apart_h2 C A5 m9 _ op2 7 CK HW9 Lo8 RRop2 eq_refl eq_refl) as IMGAPop2. cbn [fst snd ll_img LLU16 Z.sub Z.pos_sub Z.opp Pos.pred_double Z.succ_double Z.pred_double Z.double] in IMGAPop2.
  pose proof (exW_win_blk_apart_h C A5 m9 _ s 4816 op2 7 CK HW9 Lo8 eq_refl RRop2 GLO1) as WAPop2.
  assert (Fop2 : live Ar (Z_to_bv 64 op2) = None).
  { destruct (live Ar (Z_to_bv 64 op2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUB4 _ _ EE) as XX. first [discriminate Fx8 | (rewrite Fx8 in XX; discriminate XX)]. }
  pose proof Lo8 as Lop2_a5.
  assert (NMop2 : (7 mod 4 <> 0)%Z) by (intro XX; vm_compute in XX; discriminate XX).
  assert (FAop2 : live A0 (Z_to_bv 64 op2) = None).
  { destruct (live A0 (Z_to_bv 64 op2)) as [z|] eqn:EE; [|reflexivity]. exfalso. pose proof (SUBa4 _ _ EE) as XX. first [discriminate Fx8 | (rewrite Fx8 in XX; discriminate XX)]. }
  assert (SUBa5 : sub_live A0 A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op2) by (intros ->; rewrite FAop2 in Lq; discriminate Lq). rewrite (LEQ8 q NEq). exact (SUBa4 q kq Lq). }
  assert (SUB5 : sub_live Ar A5).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op2) by (intros ->; rewrite Fop2 in Lq; discriminate Lq). rewrite (LEQ8 q NEq). exact (SUB4 q kq Lq). }
  assert (NE_arr_op2 : Z_to_bv 64 arr <> Z_to_bv 64 op2) by (intros EE; pose proof Larr_a4 as XX; rewrite EE, Fx8 in XX; discriminate XX).
  assert (Larr_a5 : live A5 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ8 _ NE_arr_op2); exact Larr_a4).
  pose proof (exW_blk_apart_h C A5 m9 _ arr op2 400 7 CK HW9 Larr_a5 Lop2_a5 NE_arr_op2 RRarr RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_arr_op2.
  assert (NE_s1_op2 : Z_to_bv 64 s1 <> Z_to_bv 64 op2) by (intros EE; pose proof Ls1_a4 as XX; rewrite EE, Fx8 in XX; discriminate XX).
  assert (Ls1_a5 : live A5 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ8 _ NE_s1_op2); exact Ls1_a4).
  pose proof (exW_blk_apart_h C A5 m9 _ s1 op2 6 7 CK HW9 Ls1_a5 Lop2_a5 NE_s1_op2 RRs1 RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s1_op2.
  assert (NE_s2_op2 : Z_to_bv 64 s2 <> Z_to_bv 64 op2) by (intros EE; pose proof Ls2_a4 as XX; rewrite EE, Fx8 in XX; discriminate XX).
  assert (Ls2_a5 : live A5 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ8 _ NE_s2_op2); exact Ls2_a4).
  pose proof (exW_blk_apart_h C A5 m9 _ s2 op2 7 7 CK HW9 Ls2_a5 Lop2_a5 NE_s2_op2 RRs2 RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_s2_op2.
  assert (NE_sa_op2 : Z_to_bv 64 sa <> Z_to_bv 64 op2) by (intros EE; pose proof Lsa_a4 as XX; rewrite EE, Fx8 in XX; discriminate XX).
  assert (Lsa_a5 : live A5 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ8 _ NE_sa_op2); exact Lsa_a4).
  pose proof (exW_blk_apart_h C A5 m9 _ sa op2 24 7 CK HW9 Lsa_a5 Lop2_a5 NE_sa_op2 RRsa RRop2 ltac:(exW_cmp) ltac:(exW_cmp)) as AP_sa_op2.
  assert (PM9 : POSTM C Ar s m0 m9).
  { eapply POSTM_trans; [exact PM8|]. eapply POSTM_trans; [exact PMs8|]. apply (POSTM_sub C Ar A4 _ _ _ SUB4).
    apply (POSTM_mono C A4 (s + OFF8) s); [unfold OFF8; lia | exact PMc8]. }
  pose proof (p1_hop C A0 A4 A5 _ m9 pixd w h cm5 data cv5 (Z_to_bv 64 op2) P1s8 LEQ8 (or_introl Fx8) (or_introl (proj2 PMc8))) as P1_9.
  pose proof (p1_rest_add Ar A4 A5 pixd data cm5 cv5 _ (Z_to_bv 64 op2) PR4 LEQ8) as PR5.
  assert (KEPT8 : Forall (ex_region_kept E8 M8 m9) [(EVar 32, OFF8, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF8 4816 M8 m9 E8 (EVar 32) CK (proj1 PMc8) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M8 _ M8 m9 E8 (EVar 36) arr 400 CK HWs8 Larr_a4 RRarr eq_refl (proj2 PMc8) Larr_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M8 _ M8 m9 E8 (EVar 37) s1 6 CK HWs8 Ls1_a4 RRs1 eq_refl (proj2 PMc8) Ls1_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M8 _ M8 m9 E8 (EVar 38) s2 7 CK HWs8 Ls2_a4 RRs2 eq_refl (proj2 PMc8) Ls2_a4 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A4 A4 M8 _ M8 m9 E8 (EVar 35) sa 24 CK HWs8 Lsa_a4 RRsa eq_refl (proj2 PMc8) Lsa_a4 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E8 M8 m9 _ [] _ HKc8 KEPT8) as HKk8.
  match type of HKk8 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E8 m9 kk') in HKk8 end.
  pose (vals8 := vals7 ++ map (getr r8) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m8]).
  pose proof (regs_ok_agree 319%nat E8 (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa8.
  pose proof (exW_regs_call _ _ _ _ _ HRa8 (ex_regs_ok_junk vals8 r9 [op2; exW_canary SEGS 1410112 m9] 319%nat ltac:(vm_cast_no_check (eq_refl 319%nat))) CS8) as HRn9.
  clear HRa8.
  assert (HKa9 : know_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9 _) by (exact (know_ok_agree SEGS 319%nat E8 _ m9 _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk8)).
  try rewrite (fr_denot_agree 319%nat E8 (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) _ _ (vals_app_agree vals8 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r9 ex_r10 (EVar 351) HRn9 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact Hres8)) as HRx9. clear HRn9. rename HRx9 into HRn9.
  clear HR HK Hlf Hms HKc8 HKk8 KEPT8 HC8 HWs8 PMs8 HW8 Q10_8 Q11_8 Q1_8 Q2_8 Q4_8 PM8 PMc8 CS8 Hres8 P1s8 P1_8 PR4 MG8 TOP8 LEQ8 Hnz8 Fx8 Lo8 OFF8 RM4 SUB4 res8 Larr_a4 Ls1_a4 Ls2_a4 Lsa_a4 SUBa4.
  subst M8. clear log8. clear E8. try clear Rc8. clear KN8.
  lazymatch type of HRn9 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn9 end.
  pose proof (W_sok_win C A5 m9 _ (s - 4816) (Z.to_nat 4816) CK HW9 GLO1 GLO2) as SOK9.
  pose proof (exW_canary_ok SEGS 1410112 m9 (canary_any m9)) as CANOK9.
  pose proof (exW_kn_fixed SEGS C A5 m9 _ (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) (EVar 352) (EVar 32) (exW_canary SEGS 1410112 m9) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW9 eq_refl (proj1 CANOK9) (proj2 CANOK9) eq_refl eq_refl eq_refl SOK9 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf9.
  pose proof (exW_kn_blk SEGS C A5 m9 _ (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) (EVar 351) (EVar 32) op2 7 s 4816 65536 1347584 p16_segs CK HW9 Lop2_a5 RRop2 eq_refl eq_refl eq_refl RS ALop2 ZERO8 WAPop2 IMGAPop2) as HKb9.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9 (EVar 36) (EVar 351) arr op2 0 400 0 7 eq_refl eq_refl RRarr RRop2 AP_arr_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9))) as HKd9_arr.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9 (EVar 37) (EVar 351) s1 op2 0 6 0 7 eq_refl eq_refl RRs1 RRop2 AP_s1_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9))) as HKd9_s1.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9 (EVar 38) (EVar 351) s2 op2 0 7 0 7 eq_refl eq_refl RRs2 RRop2 AP_s2_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9))) as HKd9_s2.
  pose proof (@Forall_cons kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9) _ _ (ex_kdisj_apart SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9 (EVar 35) (EVar 351) sa op2 0 24 0 7 eq_refl eq_refl RRsa RRop2 AP_sa_op2) (@Forall_nil kentry (kentry_ok SEGS (ex_envL vals8 r9 [op2; exW_canary SEGS 1410112 m9]) m9))) as HKd9_sa.
  pose proof (proj2 (Forall_app _ _ _) (conj HKb9 (proj2 (Forall_app _ _ _) (conj HKd9_arr (proj2 (Forall_app _ _ _) (conj HKd9_s1 (proj2 (Forall_app _ _ _) (conj HKd9_s2 (proj2 (Forall_app _ _ _) (conj HKd9_sa (proj2 (Forall_app _ _ _) (conj HKf9 HKa9)))))))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn9 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN9 := kn) in HK end.
  pose proof (mcs_canary_eq C A5 m9 _ CK HW9) as CEQ9.
  exb_open HR HK ST.
  clear HR HKb9 HKd9_arr HKd9_s1 HKd9_s2 HKd9_sa HKf9 HKa9 SOK9 CANOK9 ZERO8 IMGAPop2 WAPop2 AP_arr_op2 AP_s1_op2 AP_s2_op2 AP_sa_op2.
  repeat match goal with H : getr r9 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc9 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E9 := EEx) in HR, Hlf, HK, Hms |- *; set (log9 := LLx) in Hms, Hlf; set (M9 := mem_denot E9 m9 log9) in Hms end.
  assert (WP9 : W C A5 M9 (with_vmmaps vm5 md) /\ POSTM C Ar s m9 M9).
  { subst M9. apply (exW_win_blks C A5 Ar m9 _ E9 log9 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] CK HW9 SUB5 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop2 (conj Lop2_a5 (conj Fop2 F0op2))))|].
    constructor. }
  destruct WP9 as [HWs9 PMs9].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log9 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC9 : carry log9 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc9 : know_ok SEGS E9 M9 kn1) by (apply (carry_after SEGS E9 m9 log9 kn0 [] kn1 scs hs HC9 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW9)) | exact (mp_lazy _ (w_pure _ _ _ _ HW9)) | exact Hms |].
  assert (PB9 : p1_blks_ok A0 A5 E9 [(EVar 351, op2, 7%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop2 (conj Lop2_a5 (or_intror (ex_intro _ 7%Z (conj Lop2_a5 NMop2)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A5 m9 _ E9 log9 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] pixd w h cm5 data cv5 CK HW9 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB9 P1_9) as P1s9.
  clear PB9.
  pose (BS9 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS9 HR ex_r10 Q10_9. exW_regfactB BS9 HR ex_r1 Q1_9.
  exW_cellB HK Hlf r9 BS9 (EVar 38) s2 0%Z 1%nat Cs2_0_9.
  exW_cellB HK Hlf r9 BS9 (EVar 38) s2 1%Z 1%nat Cs2_1_9.
  exW_cellB HK Hlf r9 BS9 (EVar 38) s2 2%Z 1%nat Cs2_2_9.
  exW_cellB HK Hlf r9 BS9 (EVar 38) s2 3%Z 1%nat Cs2_3_9.
  exW_cellB HK Hlf r9 BS9 (EVar 38) s2 4%Z 1%nat Cs2_4_9.
  exW_cellB HK Hlf r9 BS9 (EVar 38) s2 5%Z 1%nat Cs2_5_9.
  exW_cellB HK Hlf r9 BS9 (EVar 38) s2 6%Z 1%nat Cs2_6_9.
  clear BS9.
  lazymatch type of Q1_9 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (strlen_heap_hop6 fxk C A5 Ar M9 _ Rc9 s s2 7 32 99 51 48 46 49 (Z_to_bv 64 ra) S CK HWs9 Ls2_a5 RRs2 eq_refl eq_refl Cs2_0_9 Cs2_1_9 Cs2_2_9 Cs2_3_9 Cs2_4_9 Cs2_5_9 Cs2_6_9 Q10_9 Q1_9 ltac:(red; apply bv_eq; reflexivity)) end end.
  intros r10 m10 HW10 PMc9 EQ9 A10_9 AG9.
  pose proof (mseqt_sl_cs _ _ AG9) as CS9. clear AG9.
  assert (PM10 : POSTM C Ar s m0 m10) by (eapply POSTM_trans; [exact PM9|]; eapply POSTM_trans; [exact PMs9 | exact PMc9]).
  pose proof (p1_eq C A0 A5 _ m10 pixd w h cm5 data cv5 P1s9 EQ9) as P1_10.
  assert (KEPT9 : Forall (ex_region_kept E9 M9 m10) [(EVar 32, (-4816)%Z, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 351, 0%Z, 7%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { repeat (apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x _; exact (EQ9 x)|]). apply Forall_nil. }
  pose proof (ex_know_keepD SEGS E9 M9 m10 _ [] _ HKc9 KEPT9) as HKk9.
  match type of HKk9 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E9 m10 kk') in HKk9 end.
  pose (vals9 := vals8 ++ map (getr r9) ex_regs_list ++ map (Z_to_bv 64) [op2; exW_canary SEGS 1410112 m9]).
  pose proof (regs_ok_agree 353%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa9.
  pose proof (exW_regs_call _ _ _ _ _ HRa9 (ex_regs_ok_junk vals9 r10 [exW_canary SEGS 1410112 m10] 353%nat ltac:(vm_cast_no_check (eq_refl 353%nat))) CS9) as HRn10.
  clear HRa9.
  assert (HKa10 : know_ok SEGS (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) m10 _) by (exact (know_ok_agree SEGS 353%nat E9 _ m10 _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk9)).
  try rewrite (fr_denot_agree 353%nat E9 (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) _ _ (vals_app_agree vals9 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r10 ex_r10 (ELit 6) HRn10 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_9)) as HRx10. clear HRn10. rename HRx10 into HRn10.
  clear HR HK Hlf Hms HKc9 HKk9 KEPT9 HC9 HWs9 PMs9 HW9 Q10_9 Q1_9 PM9 PMc9 EQ9 CS9 A10_9 P1s9 P1_9 Cs2_0_9 Cs2_1_9 Cs2_2_9 Cs2_3_9 Cs2_4_9 Cs2_5_9 Cs2_6_9.
  subst M9. clear log9. clear E9. try clear Rc9. clear KN9.
  lazymatch type of HRn10 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn10 end.
  pose proof (W_sok_win C A5 m10 _ (s - 4816) (Z.to_nat 4816) CK HW10 GLO1 GLO2) as SOK10.
  pose proof (exW_canary_ok SEGS 1410112 m10 (canary_any m10)) as CANOK10.
  pose proof (exW_kn_fixed SEGS C A5 m10 _ (ex_envL vals9 r10 [exW_canary SEGS 1410112 m10]) (EVar 385) (EVar 32) (exW_canary SEGS 1410112 m10) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW10 eq_refl (proj1 CANOK10) (proj2 CANOK10) eq_refl eq_refl eq_refl SOK10 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf10.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf10 HKa10)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn10 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN10 := kn) in HK end.
  pose proof (mcs_canary_eq C A5 m10 _ CK HW10) as CEQ10.
  exb_open HR HK ST.
  clear HR HKf10 HKa10 SOK10 CANOK10.
  repeat match goal with H : getr r10 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc10 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E10 := EEx) in HR, Hlf, HK, Hms |- *; set (log10 := LLx) in Hms, Hlf; set (M10 := mem_denot E10 m10 log10) in Hms end.
  assert (WP10 : W C A5 M10 (with_vmmaps vm5 md) /\ POSTM C Ar s m10 M10).
  { subst M10. apply (exW_win_blks C A5 Ar m10 _ E10 log10 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] CK HW10 SUB5 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop2 (conj Lop2_a5 (conj Fop2 F0op2))))|].
    constructor. }
  destruct WP10 as [HWs10 PMs10].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log10 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC10 : carry log10 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc10 : know_ok SEGS E10 M10 kn1) by (apply (carry_after SEGS E10 m10 log10 kn0 [] kn1 scs hs HC10 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW10)) | exact (mp_lazy _ (w_pure _ _ _ _ HW10)) | exact Hms |].
  assert (PB10 : p1_blks_ok A0 A5 E10 [(EVar 351, op2, 7%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop2 (conj Lop2_a5 (or_intror (ex_intro _ 7%Z (conj Lop2_a5 NMop2)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A5 m10 _ E10 log10 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] pixd w h cm5 data cv5 CK HW10 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB10 P1_10) as P1s10.
  clear PB10.
  pose (BS10 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS10 HR ex_r10 Q10_10. exW_regfactB BS10 HR ex_r11 Q11_10. exW_regfactB BS10 HR ex_r12 Q12_10. exW_regfactB BS10 HR ex_r1 Q1_10.
  clear BS10.
  lazymatch type of Q10_10 with _ = Z_to_bv 64 (s + ?off) => pose (DOFF10 := off) end.
  lazymatch type of Q12_10 with _ = Z_to_bv 64 ?nn => pose (DN10 := nn) end.
  lazymatch type of Q1_10 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (mcs_memset_hop (fx := fxk) C A5 A5 M10 _ Rc10 s (s + DOFF10) DN10 (Z_to_bv 64 ra) S CK HWs10 ltac:(intros q kq Lq; exact Lq) Hhi
             ltac:(unfold DOFF10; lia) ltac:(unfold DN10; lia) ltac:(unfold DOFF10, DN10; lia) Q1_10 ltac:(red; apply bv_eq; reflexivity) Q10_10 Q11_10 Q12_10) end end.
  intros r11 m11 HW11 PMc10 A10_10 AG10 OUT10 ZER10.
  pose proof (mseqt_ms_cs _ _ AG10) as CS10. clear AG10.
  assert (PM11 : POSTM C Ar s m0 m11) by (eapply POSTM_trans; [exact PM10|]; eapply POSTM_trans; [exact PMs10 | exact (POSTM_sub C Ar A5 _ _ _ SUB5 PMc10)]).
  pose proof (p1_same C A0 A5 _ m11 pixd w h cm5 data cv5 P1s10 (proj2 PMc10)) as P1_11.
  assert (KEPT10 : Forall (ex_region_kept E10 M10 m11) [(EVar 32, (-4816)%Z, DOFF10); (EVar 32, (DOFF10 + DN10)%Z, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 351, 0%Z, 7%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x Hx; apply OUT10; intros Hy; change (edenot E10 (EVar 32)) with (Z_to_bv 64 s) in Hx; rewrite u_Z2bv in Hx by lia; unfold DOFF10, DN10 in Hx, Hy; lia|]. apply Forall_cons; [cbv beta iota delta [ex_region_kept]; intros x Hx; apply OUT10; intros Hy; change (edenot E10 (EVar 32)) with (Z_to_bv 64 s) in Hx; rewrite u_Z2bv in Hx by lia; unfold DOFF10, DN10 in Hx, Hy; lia|]. apply Forall_cons; [exact (mcs_kept_blk_win E10 M10 m11 (EVar 36) arr 400 s 4816 (s + DOFF10) (s + DOFF10 + DN10) OUT10 eq_refl RRarr (exW_win_blk_apart_h C A5 M10 _ s 4816 arr 400 CK HWs10 Larr_a5 eq_refl RRarr GLO1) ltac:(unfold DOFF10; lia) ltac:(unfold DOFF10, DN10; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E10 M10 m11 (EVar 351) op2 7 s 4816 (s + DOFF10) (s + DOFF10 + DN10) OUT10 eq_refl RRop2 (exW_win_blk_apart_h C A5 M10 _ s 4816 op2 7 CK HWs10 Lop2_a5 eq_refl RRop2 GLO1) ltac:(unfold DOFF10; lia) ltac:(unfold DOFF10, DN10; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E10 M10 m11 (EVar 37) s1 6 s 4816 (s + DOFF10) (s + DOFF10 + DN10) OUT10 eq_refl RRs1 (exW_win_blk_apart_h C A5 M10 _ s 4816 s1 6 CK HWs10 Ls1_a5 eq_refl RRs1 GLO1) ltac:(unfold DOFF10; lia) ltac:(unfold DOFF10, DN10; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E10 M10 m11 (EVar 38) s2 7 s 4816 (s + DOFF10) (s + DOFF10 + DN10) OUT10 eq_refl RRs2 (exW_win_blk_apart_h C A5 M10 _ s 4816 s2 7 CK HWs10 Ls2_a5 eq_refl RRs2 GLO1) ltac:(unfold DOFF10; lia) ltac:(unfold DOFF10, DN10; lia))|]. apply Forall_cons; [exact (mcs_kept_blk_win E10 M10 m11 (EVar 35) sa 24 s 4816 (s + DOFF10) (s + DOFF10 + DN10) OUT10 eq_refl RRsa (exW_win_blk_apart_h C A5 M10 _ s 4816 sa 24 CK HWs10 Lsa_a5 eq_refl RRsa GLO1) ltac:(unfold DOFF10; lia) ltac:(unfold DOFF10, DN10; lia))|]. apply Forall_nil. }
  pose proof (ex_know_keepD SEGS E10 M10 m11 _ [] _ HKc10 KEPT10) as HKk10.
  match type of HKk10 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E10 m11 kk') in HKk10 end.
  pose (vals10 := vals9 ++ map (getr r10) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m10]).
  pose proof (regs_ok_agree 386%nat E10 (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) _ _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa10.
  pose proof (exW_regs_call _ _ _ _ _ HRa10 (ex_regs_ok_junk vals10 r11 [exW_canary SEGS 1410112 m11] 386%nat ltac:(vm_cast_no_check (eq_refl 386%nat))) CS10) as HRn11.
  clear HRa10.
  assert (HKa11 : know_ok SEGS (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) m11 _) by (exact (know_ok_agree SEGS 386%nat E10 _ m11 _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk10)).
  try rewrite (fr_denot_agree 386%nat E10 (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) _ _ (vals_app_agree vals10 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc10 HKk10 KEPT10 HC10 HWs10 PMs10 HW10 Q10_10 Q11_10 Q12_10 Q1_10 PM10 PMc10 CS10 A10_10 OUT10 P1s10 P1_10.
  subst M10. clear log10. clear E10. try clear Rc10. clear KN10.
  lazymatch type of HRn11 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn11 end.
  pose proof (W_sok_win C A5 m11 _ (s - 4816) (Z.to_nat 4816) CK HW11 GLO1 GLO2) as SOK11.
  pose proof (exW_canary_ok SEGS 1410112 m11 (canary_any m11)) as CANOK11.
  pose proof (exW_kn_fixed SEGS C A5 m11 _ (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) (EVar 418) (EVar 32) (exW_canary SEGS 1410112 m11) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW11 eq_refl (proj1 CANOK11) (proj2 CANOK11) eq_refl eq_refl eq_refl SOK11 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf11.
  pose proof (mcs_kzero_win SEGS (ex_envL vals10 r11 [exW_canary SEGS 1410112 m11]) m11 (EVar 32) s DOFF10 DN10 eq_refl RS ltac:(unfold DOFF10; lia) eq_refl ltac:(unfold DOFF10, DN10; lia) ZER10) as HKz11.
  unfold DOFF10, DN10 in HKz11.
  pose proof (proj2 (Forall_app _ _ _) (conj HKz11 (proj2 (Forall_app _ _ _) (conj HKf11 HKa11)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn11 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN11 := kn) in HK end.
  pose proof (mcs_canary_eq C A5 m11 _ CK HW11) as CEQ11.
  exb_open HR HK ST.
  clear HR HKz11 HKf11 HKa11 SOK11 CANOK11 ZER10 DOFF10 DN10.
  repeat match goal with H : getr r11 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc11 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E11 := EEx) in HR, Hlf, HK, Hms |- *; set (log11 := LLx) in Hms, Hlf; set (M11 := mem_denot E11 m11 log11) in Hms end.
  assert (WP11 : W C A5 M11 (with_vmmaps vm5 md) /\ POSTM C Ar s m11 M11).
  { subst M11. apply (exW_win_blks C A5 Ar m11 _ E11 log11 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] CK HW11 SUB5 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop2 (conj Lop2_a5 (conj Fop2 F0op2))))|].
    constructor. }
  destruct WP11 as [HWs11 PMs11].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log11 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC11 : carry log11 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc11 : know_ok SEGS E11 M11 kn1) by (apply (carry_after SEGS E11 m11 log11 kn0 [] kn1 scs hs HC11 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW11)) | exact (mp_lazy _ (w_pure _ _ _ _ HW11)) | exact Hms |].
  assert (PB11 : p1_blks_ok A0 A5 E11 [(EVar 351, op2, 7%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop2 (conj Lop2_a5 (or_intror (ex_intro _ 7%Z (conj Lop2_a5 NMop2)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A5 m11 _ E11 log11 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] pixd w h cm5 data cv5 CK HW11 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB11 P1_11) as P1s11.
  clear PB11.
  pose (BS11 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS11 HR ex_r10 Q10_11. exW_regfactB BS11 HR ex_r11 Q11_11. exW_regfactB BS11 HR ex_r12 Q12_11. exW_regfactB BS11 HR ex_r13 Q13_11.
  exW_regfactB BS11 HR ex_r1 Q1_11. exW_regfactB BS11 HR ex_r2 Q2_11. exW_regfactB BS11 HR ex_r4 Q4_11.
  clear BS11.
  lazymatch type of Q2_11 with _ = Z_to_bv 64 (s + ?off) => pose (OFF11 := off) end.
  pose proof (RB_csc_le1 1 w h cm5) as RBl11.
  rewrite PC_CSC_eq.
  lazymatch type of Q1_11 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_11 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst (mkFP ?frk ?csk) _ _ _ _) _) _ =>
  lazymatch type of RM5 with aroom _ _ ?kk ?bb =>
    apply (HCSC frk csk C A0 A5 M11 _ Rc11 sp' pixd 30%Z 1%Z w h cm5 data cv5 (Z_to_bv 64 ret) S CK MB HWs11 SUBa5 FZ Q2_11
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CSC_STACK; lia) ltac:(lia) Q1_11 ltac:(red; apply bv_eq; reflexivity) Q4_11 Q10_11 Q11_11 Q12_11 Q13_11 (or_intror (conj eq_refl eq_refl))
             P1s11 NEpd HOK Hw1 Hh1 kk bb ltac:(rewrite with_vmmaps_vmmaps; exact RM5) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia)) end end end end.
  intros fr11 cs11 A6 m12 vm6 r12 cm11 cv11 FZc11 FS11 HW12 CS11 A10_11 SUBa6 PMc11 P1c11 CL11 CKp11 RM6.
  rewrite with_vmmaps_twice in HW12 |- *.
  pose proof (sub_live_trans Ar A0 A6 SUBr SUBa6) as SUB6.
  assert (FSA11 : forall r : reg, In (u r) fs_list -> reg_get fr11 r = reg_get fr r) by (intros r Hr; rewrite (FS11 r Hr); exact (FSA5 r Hr)).
  assert (PM12 : POSTM C Ar s m0 m12).
  { eapply POSTM_trans; [exact PM11|]. eapply POSTM_trans; [exact PMs11|]. apply (POSTM_sub C Ar A0 _ _ _ SUBr).
    apply (POSTM_mono C A0 (s + OFF11) s); [unfold OFF11; lia | exact PMc11]. }
  pose proof (p1_rest_csc C Ar A0 A5 A6 _ pixd w h data cm5 cv5 cm11 cv11 _ PR5 P1s11 SUBr CL11) as PR6.
  pose proof (p1_csc_live C A0 A5 A6 _ pixd w h data cm5 cv5 cm11 cv11 (Z_to_bv 64 arr) 400 P1s11 CL11 CKp11 Larr_a5 (or_introl (ex_intro _ 400%Z Larr_a0))) as Larr_a6.
  pose proof (p1_csc_live C A0 A5 A6 _ pixd w h data cm5 cv5 cm11 cv11 (Z_to_bv 64 op2) 7 P1s11 CL11 CKp11 Lop2_a5 (or_intror (ex_intro _ 7%Z (conj Lop2_a5 NMop2)))) as Lop2_a6.
  pose proof (p1_csc_live C A0 A5 A6 _ pixd w h data cm5 cv5 cm11 cv11 (Z_to_bv 64 s1) 6 P1s11 CL11 CKp11 Ls1_a5 (or_introl (ex_intro _ 6%Z Ls1_a0))) as Ls1_a6.
  pose proof (p1_csc_live C A0 A5 A6 _ pixd w h data cm5 cv5 cm11 cv11 (Z_to_bv 64 s2) 7 P1s11 CL11 CKp11 Ls2_a5 (or_introl (ex_intro _ 7%Z Ls2_a0))) as Ls2_a6.
  pose proof (p1_csc_live C A0 A5 A6 _ pixd w h data cm5 cv5 cm11 cv11 (Z_to_bv 64 sa) 24 P1s11 CL11 CKp11 Lsa_a5 (or_introl (ex_intro _ 24%Z Lsa_a0))) as Lsa_a6.
  assert (KEPT11 : Forall (ex_region_kept E11 M11 m12) [(EVar 32, OFF11, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF11 4816 M11 m12 E11 (EVar 32) CK (proj1 PMc11) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A5 M11 _ M11 m12 E11 (EVar 36) arr 400 CK HWs11 Larr_a5 RRarr eq_refl (proj2 PMc11) Larr_a0 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A5 M11 _ M11 m12 E11 (EVar 37) s1 6 CK HWs11 Ls1_a5 RRs1 eq_refl (proj2 PMc11) Ls1_a0 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A5 M11 _ M11 m12 E11 (EVar 38) s2 7 CK HWs11 Ls2_a5 RRs2 eq_refl (proj2 PMc11) Ls2_a0 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A0 A5 M11 _ M11 m12 E11 (EVar 35) sa 24 CK HWs11 Lsa_a5 RRsa eq_refl (proj2 PMc11) Lsa_a0 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E11 M11 m12 _ [] _ HKc11 KEPT11) as HKk11.
  match type of HKk11 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E11 m12 kk') in HKk11 end.
  pose (vals11 := vals10 ++ map (getr r11) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m11]).
  pose proof (regs_ok_agree 419%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) _ _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa11.
  pose proof (exW_regs_call _ _ _ _ _ HRa11 (ex_regs_ok_junk vals11 r12 [exW_canary SEGS 1410112 m12] 419%nat ltac:(vm_cast_no_check (eq_refl 419%nat))) CS11) as HRn12.
  clear HRa11.
  assert (HKa12 : know_ok SEGS (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) m12 _) by (exact (know_ok_agree SEGS 419%nat E11 _ m12 _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk11)).
  try rewrite (fr_denot_agree 419%nat E11 (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) _ _ (vals_app_agree vals11 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r12 ex_r10 (EVar 85) HRn12 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_11)) as HRx12. clear HRn12. rename HRx12 into HRn12.
  clear HR HK Hlf Hms HKc11 HKk11 KEPT11 HC11 HWs11 PMs11 HW11 Q10_11 Q11_11 Q12_11 Q13_11 Q1_11 Q2_11 Q4_11 PM11 PMc11 CS11 P1s11 P1_11 PR5 CL11 CKp11 OFF11 RM5 SUB5 FS11 FZ Larr_a5 Lop2_a5 Ls1_a5 Ls2_a5 Lsa_a5 SUBa5 FSA5.
  subst M11. clear log11. clear E11. try clear Rc11. clear KN11.
  lazymatch type of HRn12 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn12 end.
  pose proof (W_sok_win C A6 m12 _ (s - 4816) (Z.to_nat 4816) CK HW12 GLO1 GLO2) as SOK12.
  pose proof (exW_canary_ok SEGS 1410112 m12 (canary_any m12)) as CANOK12.
  pose proof (exW_kn_fixed SEGS C A6 m12 _ (ex_envL vals11 r12 [exW_canary SEGS 1410112 m12]) (EVar 451) (EVar 32) (exW_canary SEGS 1410112 m12) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW12 eq_refl (proj1 CANOK12) (proj2 CANOK12) eq_refl eq_refl eq_refl SOK12 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf12.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf12 HKa12)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn12 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN12 := kn) in HK end.
  pose proof (mcs_canary_eq C A6 m12 _ CK HW12) as CEQ12.
  rename FZc11 into FZ.
  rename P1c11 into P1_12.
  exb_open HR HK ST.
  clear HR HKf12 HKa12 SOK12 CANOK12.
  repeat match goal with H : getr r12 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc12 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E12 := EEx) in HR, Hlf, HK, Hms |- *; set (log12 := LLx) in Hms, Hlf; set (M12 := mem_denot E12 m12 log12) in Hms end.
  assert (WP12 : W C A6 M12 (with_vmmaps vm6 md) /\ POSTM C Ar s m12 M12).
  { subst M12. apply (exW_win_blks C A6 Ar m12 _ E12 log12 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] CK HW12 SUB6 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRop2 (conj Lop2_a6 (conj Fop2 F0op2))))|].
    constructor. }
  destruct WP12 as [HWs12 PMs12].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log12 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC12 : carry log12 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc12 : know_ok SEGS E12 M12 kn1) by (apply (carry_after SEGS E12 m12 log12 kn0 [] kn1 scs hs HC12 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW12)) | exact (mp_lazy _ (w_pure _ _ _ _ HW12)) | exact Hms |].
  assert (PB12 : p1_blks_ok A0 A6 E12 [(EVar 351, op2, 7%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRop2 (conj Lop2_a6 (or_intror (ex_intro _ 7%Z (conj Lop2_a6 NMop2)))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A6 m12 _ E12 log12 (EVar 32) s 4816 [(EVar 351, op2, 7%Z)] pixd w h cm11 data cv11 CK HW12 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB12 P1_12) as P1s12.
  clear PB12.
  pose (BS12 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS12 HR ex_r10 Q10_12. exW_regfactB BS12 HR ex_r1 Q1_12. exW_regfactB BS12 HR ex_r2 Q2_12. exW_regfactB BS12 HR ex_r4 Q4_12.
  clear BS12.
  lazymatch type of Q2_12 with _ = Z_to_bv 64 (s + ?off) => pose (OFF12 := off) end.
  lazymatch type of Q1_12 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_12 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A6 M12 _ Rc12 (Z_to_bv 64 op2) (Z_to_bv 64 ret) 7 sp' S CK HWs12 Q10_12 Lop2_a6 F0op2 Q1_12
             ltac:(red; apply bv_eq; reflexivity) Q4_12 Q2_12 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A7 m13 vm7 r13 HW13 CSx12 Ldead12 LEQ12 PMc12 RTR12.
  pose proof CSx12 as CS12. clear CSx12.
  rewrite with_vmmaps_twice in HW13 |- *.
  assert (SUB7 : sub_live Ar A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op2) by (intros ->; rewrite Fop2 in Lq; discriminate Lq). rewrite (LEQ12 q NEq). exact (SUB6 q kq Lq). }
  assert (SUBa7 : sub_live A0 A7).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 op2) by (intros ->; rewrite FAop2 in Lq; discriminate Lq). rewrite (LEQ12 q NEq). exact (SUBa6 q kq Lq). }
  assert (Larr_a7 : live A7 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ12 _ NE_arr_op2); exact Larr_a6).
  assert (Ls1_a7 : live A7 (Z_to_bv 64 s1) = Some 6%Z) by (rewrite (LEQ12 _ NE_s1_op2); exact Ls1_a6).
  assert (Ls2_a7 : live A7 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ12 _ NE_s2_op2); exact Ls2_a6).
  assert (Lsa_a7 : live A7 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ12 _ NE_sa_op2); exact Lsa_a6).
  assert (PM13 : POSTM C Ar s m0 m13).
  { eapply POSTM_trans; [exact PM12|]. eapply POSTM_trans; [exact PMs12|]. apply (POSTM_sub C Ar A7 _ _ _ SUB7).
    apply (POSTM_mono C A7 (s + OFF12) s); [unfold OFF12; lia | exact PMc12]. }
  pose proof (RTR12 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM6) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia)) as RM7. rewrite !Z.sub_0_r in RM7.
  pose proof (p1_hop C A0 A6 A7 _ m13 pixd w h cm11 data cv11 (Z_to_bv 64 op2) P1s12 LEQ12 (or_intror (or_intror (ex_intro _ 7%Z (conj Lop2_a6 NMop2)))) (or_intror (proj2 PMc12))) as P1_13.
  pose proof (p1_rest_del Ar A6 A7 pixd data cm11 cv11 [Z_to_bv 64 op2; Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] (Z_to_bv 64 op2) PR6 LEQ12 Ldead12 Fop2 ltac:(intros q Hq; cbn [In] in Hq |- *; tauto)) as PR7.
  assert (KEPT12 : Forall (ex_region_kept E12 M12 m13) [(EVar 32, OFF12, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 37, 0%Z, 6%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF12 4816 M12 m13 E12 (EVar 32) CK (proj1 PMc12) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m13 _ M12 m13 E12 (EVar 36) arr 400 CK HW13 Larr_a7 RRarr eq_refl (proj2 PMc12) Larr_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m13 _ M12 m13 E12 (EVar 37) s1 6 CK HW13 Ls1_a7 RRs1 eq_refl (proj2 PMc12) Ls1_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m13 _ M12 m13 E12 (EVar 38) s2 7 CK HW13 Ls2_a7 RRs2 eq_refl (proj2 PMc12) Ls2_a7 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A7 A7 m13 _ M12 m13 E12 (EVar 35) sa 24 CK HW13 Lsa_a7 RRsa eq_refl (proj2 PMc12) Lsa_a7 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E12 M12 m13 _ [] _ HKc12 KEPT12) as HKk12.
  match type of HKk12 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E12 m13 kk') in HKk12 end.
  pose (vals12 := vals11 ++ map (getr r12) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m12]).
  pose proof (regs_ok_agree 452%nat E12 (ex_envL vals12 r13 [exW_canary SEGS 1410112 m13]) _ _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa12.
  pose proof (exW_regs_call _ _ _ _ _ HRa12 (ex_regs_ok_junk vals12 r13 [exW_canary SEGS 1410112 m13] 452%nat ltac:(vm_cast_no_check (eq_refl 452%nat))) CS12) as HRn13.
  clear HRa12.
  assert (HKa13 : know_ok SEGS (ex_envL vals12 r13 [exW_canary SEGS 1410112 m13]) m13 _) by (exact (know_ok_agree SEGS 452%nat E12 _ m13 _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk12)).
  try rewrite (fr_denot_agree 452%nat E12 (ex_envL vals12 r13 [exW_canary SEGS 1410112 m13]) _ _ (vals_app_agree vals12 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc12 HKk12 KEPT12 HC12 HWs12 PMs12 HW12 Q10_12 Q1_12 Q2_12 Q4_12 PM12 PMc12 CS12 P1s12 P1_12 PR6 LEQ12 Ldead12 RTR12 OFF12 RM6 SUB6 Larr_a6 Ls1_a6 Ls2_a6 Lsa_a6 Lop2_a6 SUBa6.
  subst M12. clear log12. clear E12. try clear Rc12. clear KN12.
  lazymatch type of HRn13 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn13 end.
  pose proof (W_sok_win C A7 m13 _ (s - 4816) (Z.to_nat 4816) CK HW13 GLO1 GLO2) as SOK13.
  pose proof (exW_canary_ok SEGS 1410112 m13 (canary_any m13)) as CANOK13.
  pose proof (exW_kn_fixed SEGS C A7 m13 _ (ex_envL vals12 r13 [exW_canary SEGS 1410112 m13]) (EVar 484) (EVar 32) (exW_canary SEGS 1410112 m13) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW13 eq_refl (proj1 CANOK13) (proj2 CANOK13) eq_refl eq_refl eq_refl SOK13 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf13.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf13 HKa13)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn13 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN13 := kn) in HK end.
  pose proof (mcs_canary_eq C A7 m13 _ CK HW13) as CEQ13.
  exb_open HR HK ST.
  clear HR HKf13 HKa13 SOK13 CANOK13.
  repeat match goal with H : getr r13 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc13 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E13 := EEx) in HR, Hlf, HK, Hms |- *; set (log13 := LLx) in Hms, Hlf; set (M13 := mem_denot E13 m13 log13) in Hms end.
  assert (WP13 : W C A7 M13 (with_vmmaps vm7 md) /\ POSTM C Ar s m13 M13).
  { subst M13. apply (exW_win_blks C A7 Ar m13 _ E13 log13 (EVar 32) s 4816 [(EVar 35, sa, 24%Z)] CK HW13 SUB7 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor; [exact (conj eq_refl (conj RRsa (conj Lsa_a7 (conj Fsa F0sa))))|].
    constructor. }
  destruct WP13 as [HWs13 PMs13].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log13 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC13 : carry log13 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc13 : know_ok SEGS E13 M13 kn1) by (apply (carry_after SEGS E13 m13 log13 kn0 [] kn1 scs hs HC13 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW13)) | exact (mp_lazy _ (w_pure _ _ _ _ HW13)) | exact Hms |].
  assert (PB13 : p1_blks_ok A0 A7 E13 [(EVar 35, sa, 24%Z)]).
  { unfold p1_blks_ok. constructor; [cbv beta iota; refine (conj _ (conj RRsa (conj Lsa_a7 (or_introl (ex_intro _ 24%Z Lsa_a0))))); reflexivity|]. constructor. }
  pose proof (p1_sess C A0 A7 m13 _ E13 log13 (EVar 32) s 4816 [(EVar 35, sa, 24%Z)] pixd w h cm11 data cv11 CK HW13 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS PB13 P1_13) as P1s13.
  clear PB13.
  pose (BS13 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS13 HR ex_r10 Q10_13. exW_regfactB BS13 HR ex_r1 Q1_13. exW_regfactB BS13 HR ex_r2 Q2_13. exW_regfactB BS13 HR ex_r4 Q4_13.
  clear BS13.
  lazymatch type of Q2_13 with _ = Z_to_bv 64 (s + ?off) => pose (OFF13 := off) end.
  lazymatch type of Q1_13 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_13 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A7 M13 _ Rc13 (Z_to_bv 64 s1) (Z_to_bv 64 ret) 6 sp' S CK HWs13 Q10_13 Ls1_a7 F0s1 Q1_13
             ltac:(red; apply bv_eq; reflexivity) Q4_13 Q2_13 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A8 m14 vm8 r14 HW14 CSx13 Ldead13 LEQ13 PMc13 RTR13.
  pose proof CSx13 as CS13. clear CSx13.
  rewrite with_vmmaps_twice in HW14 |- *.
  assert (SUB8 : sub_live Ar A8).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 s1) by (intros ->; rewrite Fs1 in Lq; discriminate Lq). rewrite (LEQ13 q NEq). exact (SUB7 q kq Lq). }
  assert (Larr_a8 : live A8 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ13 _ NE_arr_s1); exact Larr_a7).
  assert (Ls2_a8 : live A8 (Z_to_bv 64 s2) = Some 7%Z) by (rewrite (LEQ13 _ (not_eq_sym NE_s1_s2)); exact Ls2_a7).
  assert (Lsa_a8 : live A8 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ13 _ NE_sa_s1); exact Lsa_a7).
  assert (PM14 : POSTM C Ar s m0 m14).
  { eapply POSTM_trans; [exact PM13|]. eapply POSTM_trans; [exact PMs13|]. apply (POSTM_sub C Ar A8 _ _ _ SUB8).
    apply (POSTM_mono C A8 (s + OFF13) s); [unfold OFF13; lia | exact PMc13]. }
  pose proof (RTR13 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM7) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia)) as RM8. rewrite !Z.sub_0_r in RM8.
  pose proof (p1_hop C A0 A7 A8 _ m14 pixd w h cm11 data cv11 (Z_to_bv 64 s1) P1s13 LEQ13 (or_intror (or_introl (ex_intro _ 6%Z Ls1_a0))) (or_intror (proj2 PMc13))) as P1_14.
  pose proof (p1_rest_del Ar A7 A8 pixd data cm11 cv11 [Z_to_bv 64 s2; Z_to_bv 64 s1; Z_to_bv 64 arr; Z_to_bv 64 sa] [Z_to_bv 64 s2; Z_to_bv 64 arr; Z_to_bv 64 sa] (Z_to_bv 64 s1) PR7 LEQ13 Ldead13 Fs1 ltac:(intros q Hq; cbn [In] in Hq |- *; tauto)) as PR8.
  assert (KEPT13 : Forall (ex_region_kept E13 M13 m14) [(EVar 32, OFF13, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 38, 0%Z, 7%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF13 4816 M13 m14 E13 (EVar 32) CK (proj1 PMc13) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 m14 _ M13 m14 E13 (EVar 36) arr 400 CK HW14 Larr_a8 RRarr eq_refl (proj2 PMc13) Larr_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 m14 _ M13 m14 E13 (EVar 38) s2 7 CK HW14 Ls2_a8 RRs2 eq_refl (proj2 PMc13) Ls2_a8 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A8 A8 m14 _ M13 m14 E13 (EVar 35) sa 24 CK HW14 Lsa_a8 RRsa eq_refl (proj2 PMc13) Lsa_a8 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E13 M13 m14 _ [] _ HKc13 KEPT13) as HKk13.
  match type of HKk13 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E13 m14 kk') in HKk13 end.
  pose (vals13 := vals12 ++ map (getr r13) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m13]).
  pose proof (regs_ok_agree 485%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) _ _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa13.
  pose proof (exW_regs_call _ _ _ _ _ HRa13 (ex_regs_ok_junk vals13 r14 [exW_canary SEGS 1410112 m14] 485%nat ltac:(vm_cast_no_check (eq_refl 485%nat))) CS13) as HRn14.
  clear HRa13.
  assert (HKa14 : know_ok SEGS (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) m14 _) by (exact (know_ok_agree SEGS 485%nat E13 _ m14 _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk13)).
  try rewrite (fr_denot_agree 485%nat E13 (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) _ _ (vals_app_agree vals13 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc13 HKk13 KEPT13 HC13 HWs13 PMs13 HW13 Q10_13 Q1_13 Q2_13 Q4_13 PM13 PMc13 CS13 P1s13 P1_13 PR7 LEQ13 Ldead13 RTR13 OFF13 RM7 SUB7 Larr_a7 Ls2_a7 Lsa_a7 Ls1_a7 SUBa7.
  subst M13. clear log13. clear E13. try clear Rc13. clear KN13.
  lazymatch type of HRn14 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn14 end.
  pose proof (W_sok_win C A8 m14 _ (s - 4816) (Z.to_nat 4816) CK HW14 GLO1 GLO2) as SOK14.
  pose proof (exW_canary_ok SEGS 1410112 m14 (canary_any m14)) as CANOK14.
  pose proof (exW_kn_fixed SEGS C A8 m14 _ (ex_envL vals13 r14 [exW_canary SEGS 1410112 m14]) (EVar 517) (EVar 32) (exW_canary SEGS 1410112 m14) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW14 eq_refl (proj1 CANOK14) (proj2 CANOK14) eq_refl eq_refl eq_refl SOK14 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf14.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf14 HKa14)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn14 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN14 := kn) in HK end.
  pose proof (mcs_canary_eq C A8 m14 _ CK HW14) as CEQ14.
  exb_open HR HK ST.
  clear HR HKf14 HKa14 SOK14 CANOK14.
  repeat match goal with H : getr r14 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc14 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E14 := EEx) in HR, Hlf, HK, Hms |- *; set (log14 := LLx) in Hms, Hlf; set (M14 := mem_denot E14 m14 log14) in Hms end.
  assert (WP14 : W C A8 M14 (with_vmmaps vm8 md) /\ POSTM C Ar s m14 M14).
  { subst M14. apply (exW_win_blks C A8 Ar m14 _ E14 log14 (EVar 32) s 4816 [] CK HW14 SUB8 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP14 as [HWs14 PMs14].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log14 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC14 : carry log14 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc14 : know_ok SEGS E14 M14 kn1) by (apply (carry_after SEGS E14 m14 log14 kn0 [] kn1 scs hs HC14 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW14)) | exact (mp_lazy _ (w_pure _ _ _ _ HW14)) | exact Hms |].
  pose proof (p1_sess C A0 A8 m14 _ E14 log14 (EVar 32) s 4816 [] pixd w h cm11 data cv11 CK HW14 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_14) as P1s14.
  pose (BS14 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS14 HR ex_r10 Q10_14. exW_regfactB BS14 HR ex_r1 Q1_14. exW_regfactB BS14 HR ex_r2 Q2_14. exW_regfactB BS14 HR ex_r4 Q4_14.
  clear BS14.
  lazymatch type of Q2_14 with _ = Z_to_bv 64 (s + ?off) => pose (OFF14 := off) end.
  lazymatch type of Q1_14 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_14 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A8 M14 _ Rc14 (Z_to_bv 64 s2) (Z_to_bv 64 ret) 7 sp' S CK HWs14 Q10_14 Ls2_a8 F0s2 Q1_14
             ltac:(red; apply bv_eq; reflexivity) Q4_14 Q2_14 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A9 m15 vm9 r15 HW15 CSx14 Ldead14 LEQ14 PMc14 RTR14.
  pose proof CSx14 as CS14. clear CSx14.
  rewrite with_vmmaps_twice in HW15 |- *.
  assert (SUB9 : sub_live Ar A9).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 s2) by (intros ->; rewrite Fs2 in Lq; discriminate Lq). rewrite (LEQ14 q NEq). exact (SUB8 q kq Lq). }
  assert (Larr_a9 : live A9 (Z_to_bv 64 arr) = Some 400%Z) by (rewrite (LEQ14 _ NE_arr_s2); exact Larr_a8).
  assert (Lsa_a9 : live A9 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ14 _ NE_sa_s2); exact Lsa_a8).
  assert (PM15 : POSTM C Ar s m0 m15).
  { eapply POSTM_trans; [exact PM14|]. eapply POSTM_trans; [exact PMs14|]. apply (POSTM_sub C Ar A9 _ _ _ SUB9).
    apply (POSTM_mono C A9 (s + OFF14) s); [unfold OFF14; lia | exact PMc14]. }
  pose proof (RTR14 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM8) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia)) as RM9. rewrite !Z.sub_0_r in RM9.
  pose proof (p1_hop C A0 A8 A9 _ m15 pixd w h cm11 data cv11 (Z_to_bv 64 s2) P1s14 LEQ14 (or_intror (or_introl (ex_intro _ 7%Z Ls2_a0))) (or_intror (proj2 PMc14))) as P1_15.
  pose proof (p1_rest_del Ar A8 A9 pixd data cm11 cv11 [Z_to_bv 64 s2; Z_to_bv 64 arr; Z_to_bv 64 sa] [Z_to_bv 64 arr; Z_to_bv 64 sa] (Z_to_bv 64 s2) PR8 LEQ14 Ldead14 Fs2 ltac:(intros q Hq; cbn [In] in Hq |- *; tauto)) as PR9.
  assert (KEPT14 : Forall (ex_region_kept E14 M14 m15) [(EVar 32, OFF14, 0%Z); (EVar 36, 0%Z, 400%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF14 4816 M14 m15 E14 (EVar 32) CK (proj1 PMc14) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 m15 _ M14 m15 E14 (EVar 36) arr 400 CK HW15 Larr_a9 RRarr eq_refl (proj2 PMc14) Larr_a9 eq_refl)|]. constructor; [exact (exW_kept_blk2 C A9 A9 m15 _ M14 m15 E14 (EVar 35) sa 24 CK HW15 Lsa_a9 RRsa eq_refl (proj2 PMc14) Lsa_a9 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E14 M14 m15 _ [] _ HKc14 KEPT14) as HKk14.
  match type of HKk14 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E14 m15 kk') in HKk14 end.
  pose (vals14 := vals13 ++ map (getr r14) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m14]).
  pose proof (regs_ok_agree 518%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) _ _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa14.
  pose proof (exW_regs_call _ _ _ _ _ HRa14 (ex_regs_ok_junk vals14 r15 [exW_canary SEGS 1410112 m15] 518%nat ltac:(vm_cast_no_check (eq_refl 518%nat))) CS14) as HRn15.
  clear HRa14.
  assert (HKa15 : know_ok SEGS (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) m15 _) by (exact (know_ok_agree SEGS 518%nat E14 _ m15 _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk14)).
  try rewrite (fr_denot_agree 518%nat E14 (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) _ _ (vals_app_agree vals14 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc14 HKk14 KEPT14 HC14 HWs14 PMs14 HW14 Q10_14 Q1_14 Q2_14 Q4_14 PM14 PMc14 CS14 P1s14 P1_14 PR8 LEQ14 Ldead14 RTR14 OFF14 RM8 SUB8 Larr_a8 Lsa_a8 Ls2_a8.
  subst M14. clear log14. clear E14. try clear Rc14. clear KN14.
  lazymatch type of HRn15 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn15 end.
  pose proof (W_sok_win C A9 m15 _ (s - 4816) (Z.to_nat 4816) CK HW15 GLO1 GLO2) as SOK15.
  pose proof (exW_canary_ok SEGS 1410112 m15 (canary_any m15)) as CANOK15.
  pose proof (exW_kn_fixed SEGS C A9 m15 _ (ex_envL vals14 r15 [exW_canary SEGS 1410112 m15]) (EVar 550) (EVar 32) (exW_canary SEGS 1410112 m15) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW15 eq_refl (proj1 CANOK15) (proj2 CANOK15) eq_refl eq_refl eq_refl SOK15 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf15.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf15 HKa15)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn15 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN15 := kn) in HK end.
  pose proof (mcs_canary_eq C A9 m15 _ CK HW15) as CEQ15.
  exb_open HR HK ST.
  clear HR HKf15 HKa15 SOK15 CANOK15.
  repeat match goal with H : getr r15 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc15 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E15 := EEx) in HR, Hlf, HK, Hms |- *; set (log15 := LLx) in Hms, Hlf; set (M15 := mem_denot E15 m15 log15) in Hms end.
  assert (WP15 : W C A9 M15 (with_vmmaps vm9 md) /\ POSTM C Ar s m15 M15).
  { subst M15. apply (exW_win_blks C A9 Ar m15 _ E15 log15 (EVar 32) s 4816 [] CK HW15 SUB9 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP15 as [HWs15 PMs15].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log15 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC15 : carry log15 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc15 : know_ok SEGS E15 M15 kn1) by (apply (carry_after SEGS E15 m15 log15 kn0 [] kn1 scs hs HC15 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW15)) | exact (mp_lazy _ (w_pure _ _ _ _ HW15)) | exact Hms |].
  pose proof (p1_sess C A0 A9 m15 _ E15 log15 (EVar 32) s 4816 [] pixd w h cm11 data cv11 CK HW15 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_15) as P1s15.
  pose (BS15 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS15 HR ex_r10 Q10_15. exW_regfactB BS15 HR ex_r1 Q1_15. exW_regfactB BS15 HR ex_r2 Q2_15. exW_regfactB BS15 HR ex_r4 Q4_15.
  clear BS15.
  lazymatch type of Q2_15 with _ = Z_to_bv 64 (s + ?off) => pose (OFF15 := off) end.
  lazymatch type of Q1_15 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_15 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A9 M15 _ Rc15 (Z_to_bv 64 arr) (Z_to_bv 64 ret) 400 sp' S CK HWs15 Q10_15 Larr_a9 F0arr Q1_15
             ltac:(red; apply bv_eq; reflexivity) Q4_15 Q2_15 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A10 m16 vm10 r16 HW16 CSx15 Ldead15 LEQ15 PMc15 RTR15.
  pose proof CSx15 as CS15. clear CSx15.
  rewrite with_vmmaps_twice in HW16 |- *.
  assert (SUB10 : sub_live Ar A10).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 arr) by (intros ->; rewrite Farr in Lq; discriminate Lq). rewrite (LEQ15 q NEq). exact (SUB9 q kq Lq). }
  assert (Lsa_a10 : live A10 (Z_to_bv 64 sa) = Some 24%Z) by (rewrite (LEQ15 _ NE_sa_arr); exact Lsa_a9).
  assert (PM16 : POSTM C Ar s m0 m16).
  { eapply POSTM_trans; [exact PM15|]. eapply POSTM_trans; [exact PMs15|]. apply (POSTM_sub C Ar A10 _ _ _ SUB10).
    apply (POSTM_mono C A10 (s + OFF15) s); [unfold OFF15; lia | exact PMc15]. }
  pose proof (RTR15 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM9) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia)) as RM10. rewrite !Z.sub_0_r in RM10.
  pose proof (p1_hop C A0 A9 A10 _ m16 pixd w h cm11 data cv11 (Z_to_bv 64 arr) P1s15 LEQ15 (or_intror (or_introl (ex_intro _ 400%Z Larr_a0))) (or_intror (proj2 PMc15))) as P1_16.
  pose proof (p1_rest_del Ar A9 A10 pixd data cm11 cv11 [Z_to_bv 64 arr; Z_to_bv 64 sa] [Z_to_bv 64 sa] (Z_to_bv 64 arr) PR9 LEQ15 Ldead15 Farr ltac:(intros q Hq; cbn [In] in Hq |- *; tauto)) as PR10.
  assert (KEPT15 : Forall (ex_region_kept E15 M15 m16) [(EVar 32, OFF15, 0%Z); (EVar 35, 0%Z, 24%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF15 4816 M15 m16 E15 (EVar 32) CK (proj1 PMc15) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor; [exact (exW_kept_blk2 C A10 A10 m16 _ M15 m16 E15 (EVar 35) sa 24 CK HW16 Lsa_a10 RRsa eq_refl (proj2 PMc15) Lsa_a10 eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E15 M15 m16 _ [] _ HKc15 KEPT15) as HKk15.
  match type of HKk15 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E15 m16 kk') in HKk15 end.
  pose (vals15 := vals14 ++ map (getr r15) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m15]).
  pose proof (regs_ok_agree 551%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) _ _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa15.
  pose proof (exW_regs_call _ _ _ _ _ HRa15 (ex_regs_ok_junk vals15 r16 [exW_canary SEGS 1410112 m16] 551%nat ltac:(vm_cast_no_check (eq_refl 551%nat))) CS15) as HRn16.
  clear HRa15.
  assert (HKa16 : know_ok SEGS (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) m16 _) by (exact (know_ok_agree SEGS 551%nat E15 _ m16 _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk15)).
  try rewrite (fr_denot_agree 551%nat E15 (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) _ _ (vals_app_agree vals15 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc15 HKk15 KEPT15 HC15 HWs15 PMs15 HW15 Q10_15 Q1_15 Q2_15 Q4_15 PM15 PMc15 CS15 P1s15 P1_15 PR9 LEQ15 Ldead15 RTR15 OFF15 RM9 SUB9 Lsa_a9 Larr_a9.
  subst M15. clear log15. clear E15. try clear Rc15. clear KN15.
  lazymatch type of HRn16 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn16 end.
  pose proof (W_sok_win C A10 m16 _ (s - 4816) (Z.to_nat 4816) CK HW16 GLO1 GLO2) as SOK16.
  pose proof (exW_canary_ok SEGS 1410112 m16 (canary_any m16)) as CANOK16.
  pose proof (exW_kn_fixed SEGS C A10 m16 _ (ex_envL vals15 r16 [exW_canary SEGS 1410112 m16]) (EVar 583) (EVar 32) (exW_canary SEGS 1410112 m16) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW16 eq_refl (proj1 CANOK16) (proj2 CANOK16) eq_refl eq_refl eq_refl SOK16 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf16.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf16 HKa16)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn16 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN16 := kn) in HK end.
  pose proof (mcs_canary_eq C A10 m16 _ CK HW16) as CEQ16.
  exb_open HR HK ST.
  clear HR HKf16 HKa16 SOK16 CANOK16.
  repeat match goal with H : getr r16 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_exit ST Rc16 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E16 := EEx) in HR, Hlf, HK, Hms |- *; set (log16 := LLx) in Hms, Hlf; set (M16 := mem_denot E16 m16 log16) in Hms end.
  assert (WP16 : W C A10 M16 (with_vmmaps vm10 md) /\ POSTM C Ar s m16 M16).
  { subst M16. apply (exW_win_blks C A10 Ar m16 _ E16 log16 (EVar 32) s 4816 [] CK HW16 SUB10 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |].
    constructor. }
  destruct WP16 as [HWs16 PMs16].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log16 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC16 : carry log16 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc16 : know_ok SEGS E16 M16 kn1) by (apply (carry_after SEGS E16 m16 log16 kn0 [] kn1 scs hs HC16 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW16)) | exact (mp_lazy _ (w_pure _ _ _ _ HW16)) | exact Hms |].
  pose proof (p1_sess C A0 A10 m16 _ E16 log16 (EVar 32) s 4816 [] pixd w h cm11 data cv11 CK HW16 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_16) as P1s16.
  pose (BS16 := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BS16 HR ex_r10 Q10_16. exW_regfactB BS16 HR ex_r1 Q1_16. exW_regfactB BS16 HR ex_r2 Q2_16. exW_regfactB BS16 HR ex_r4 Q4_16.
  clear BS16.
  lazymatch type of Q2_16 with _ = Z_to_bv 64 (s + ?off) => pose (OFF16 := off) end.
  lazymatch type of Q1_16 with _ = Z_to_bv 64 ?ret => lazymatch type of Q2_16 with _ = Z_to_bv 64 ?sp' => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (W_free16 (fx := fxk) C A10 M16 _ Rc16 (Z_to_bv 64 sa) (Z_to_bv 64 ret) 24 sp' S CK HWs16 Q10_16 Lsa_a10 F0sa Q1_16
             ltac:(red; apply bv_eq; reflexivity) Q4_16 Q2_16 ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)) end end end.
  intros A11 m17 vm11 r17 HW17 CSx16 Ldead16 LEQ16 PMc16 RTR16.
  pose proof CSx16 as CS16. clear CSx16.
  rewrite with_vmmaps_twice in HW17 |- *.
  assert (SUB11 : sub_live Ar A11).
  { intros q kq Lq. assert (NEq : q <> Z_to_bv 64 sa) by (intros ->; rewrite Fsa in Lq; discriminate Lq). rewrite (LEQ16 q NEq). exact (SUB10 q kq Lq). }
  assert (PM17 : POSTM C Ar s m0 m17).
  { eapply POSTM_trans; [exact PM16|]. eapply POSTM_trans; [exact PMs16|]. apply (POSTM_sub C Ar A11 _ _ _ SUB11).
    apply (POSTM_mono C A11 (s + OFF16) s); [unfold OFF16; lia | exact PMc16]. }
  pose proof (RTR16 _ _ ltac:(rewrite with_vmmaps_vmmaps; exact RM10) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia)) as RM11. rewrite !Z.sub_0_r in RM11.
  pose proof (p1_hop C A0 A10 A11 _ m17 pixd w h cm11 data cv11 (Z_to_bv 64 sa) P1s16 LEQ16 (or_intror (or_introl (ex_intro _ 24%Z Lsa_a0))) (or_intror (proj2 PMc16))) as P1_17.
  pose proof (p1_rest_del Ar A10 A11 pixd data cm11 cv11 [Z_to_bv 64 sa] [] (Z_to_bv 64 sa) PR10 LEQ16 Ldead16 Fsa ltac:(intros q Hq; cbn [In] in Hq |- *; tauto)) as PR11.
  assert (KEPT16 : Forall (ex_region_kept E16 M16 m17) [(EVar 32, OFF16, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF16 4816 M16 m17 E16 (EVar 32) CK (proj1 PMc16) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E16 M16 m17 _ [] _ HKc16 KEPT16) as HKk16.
  match type of HKk16 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E16 m17 kk') in HKk16 end.
  pose (vals16 := vals15 ++ map (getr r16) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 1410112 m16]).
  pose proof (regs_ok_agree 584%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 1410112 m17]) _ _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa16.
  pose proof (exW_regs_call _ _ _ _ _ HRa16 (ex_regs_ok_junk vals16 r17 [exW_canary SEGS 1410112 m17] 584%nat ltac:(vm_cast_no_check (eq_refl 584%nat))) CS16) as HRn17.
  clear HRa16.
  assert (HKa17 : know_ok SEGS (ex_envL vals16 r17 [exW_canary SEGS 1410112 m17]) m17 _) by (exact (know_ok_agree SEGS 584%nat E16 _ m17 _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk16)).
  try rewrite (fr_denot_agree 584%nat E16 (ex_envL vals16 r17 [exW_canary SEGS 1410112 m17]) _ _ (vals_app_agree vals16 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc16 HKk16 KEPT16 HC16 HWs16 PMs16 HW16 Q10_16 Q1_16 Q2_16 Q4_16 PM16 PMc16 CS16 P1s16 P1_16 PR10 LEQ16 Ldead16 RTR16 OFF16 RM10 SUB10 Lsa_a10.
  subst M16. clear log16. clear E16. try clear Rc16. clear KN16.
  lazymatch type of HRn17 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn17 end.
  pose proof (W_sok_win C A11 m17 _ (s - 4816) (Z.to_nat 4816) CK HW17 GLO1 GLO2) as SOK17.
  pose proof (exW_canary_ok SEGS 1410112 m17 (canary_any m17)) as CANOK17.
  pose proof (exW_kn_fixed SEGS C A11 m17 _ (ex_envL vals16 r17 [exW_canary SEGS 1410112 m17]) (EVar 616) (EVar 32) (exW_canary SEGS 1410112 m17) s 4816 1410112 65536 1191936 1206800 1207320 1206800 1207320
                HW17 eq_refl (proj1 CANOK17) (proj2 CANOK17) eq_refl eq_refl eq_refl SOK17 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf17.
  pose proof (proj2 (Forall_app _ _ _) (conj HKf17 HKa17)) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn17 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN17 := kn) in HK end.
  pose proof (mcs_canary_eq C A11 m17 _ CK HW17) as CEQ17.
  exb_open HR HK ST.
  clear HR HKf17 HKa17 SOK17 CANOK17.
  repeat match goal with H : getr r17 _ = _ |- _ => clear H end.
  td_drive 2000%nat 6000%nat STOPS2 FDEF HK ST FZ.
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E17 := EEx) in HR, Hlf, HK, Hms |- *; set (log17 := LLx) in Hms, Hlf; set (M17 := mem_denot E17 m17 log17) in Hms end.
  assert (WP17 : W C A11 M17 (with_vmmaps vm11 md) /\ POSTM C Ar s m17 M17).
  { subst M17. apply (exW_win_blks C A11 Ar m17 _ E17 log17 (EVar 32) s 4816 [] CK HW17 SUB11 Hlf); [vm_compute; reflexivity | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP17 as [HWs17 PMs17].
  pose proof (p1_sess C A0 A11 m17 _ E17 log17 (EVar 32) s 4816 [] pixd w h cm11 data cv11 CK HW17 GLO1 Hlf ltac:(vm_compute; reflexivity) eq_refl RS (Forall_nil _) P1_17) as P1s17.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW17)) | exact (mp_lazy _ (w_pure _ _ _ _ HW17)) | exact Hms |].
  pose (BSF := [(32%nat, s); (34%nat, pixs); (35%nat, sa); (36%nat, arr); (37%nat, s1); (38%nat, s2); (85%nat, pixd); (152%nat, op1); (351%nat, op2)]).
  exW_regfactB BSF HR ex_r10 G10. clear BSF.
  lazymatch type of RM11 with aroom ?AA ?VV ?kk ?bb =>
    assert (RMF : aroom AA VV (kR - RK_mseqt) (bR - RB_mseqt w h cm))
      by (pose proof (roomtr_refl AA VV 0 (bb - (bR - RB_mseqt w h cm)) ltac:(lia) ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) kk bb RM11 ltac:(clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia) ltac:(lia)) as RT2;
          replace (kR - RK_mseqt)%Z with (kk - 0)%Z by (clear - HkR HbR RKc8 RKc1 RBc8 RBc1 RBl5 RBl11; unfold RK_mseqt, RB_mseqt in *; lia);
          replace (bR - RB_mseqt w h cm)%Z with (bb - (bb - (bR - RB_mseqt w h cm)))%Z by lia; exact RT2) end.
  lazymatch goal with |- realizes _ (mkCfg (@mkst (mkFP ?frk ?csk) _ _ _ _) _) _ =>
    refine (HC frk csk A11 M17 vm11 RcF pixd cm11 data cv11 FZ (fun r Hr => FSA11 r Hr) HWs17 _ G10 SUB11 (POSTM_trans _ _ _ _ _ _ PM17 PMs17) P1s17 NEpd PR11 RMF) end.
  lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exT_cs_of_al EE sr regsE RcF [(2%nat, EVar 32); (3%nat, EVar 3); (4%nat, ELit 1278416); (8%nat, EVar 40); (9%nat, EVar 41); (18%nat, EVar 42); (19%nat, EVar 43); (20%nat, EVar 44); (21%nat, EVar 45); (22%nat, EVar 46); (23%nat, EVar 47); (24%nat, EVar 48); (25%nat, EVar 49); (26%nat, EVar 50); (27%nat, EVar 51)] HR) end.
  { constructor; [symmetry; exact HE2k|]. constructor; [exact HG3|]. constructor; [symmetry; exact HE4k|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor; [exact (WalksLib.zbv_self _)|]. constructor. }
  { vm_compute; reflexivity. }
Qed.
End Tail.
End Chain.
