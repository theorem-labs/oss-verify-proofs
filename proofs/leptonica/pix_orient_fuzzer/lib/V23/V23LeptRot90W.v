(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require SeqExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyTR.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptCmap2 O23LeptPixHdrT2 O23LeptRot90 O23LeptRot90W.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptUb V23LeptRot90.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptErr V23LeptCmap2 V23LeptPixCreateT2 V23LeptPixCopyA V23LeptRot90cwW V23LeptRot90ccwW.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_r90_pixd : str16 0x126da 13.
Proof. str16_tac. Qed.
Lemma str_r90 : str16 0x193f3 11.
Proof. str16_tac. Qed.

Lemma wpl1_626 : forall h : Z, (1 <= h <= 20000)%Z -> (wpl_of h 1 <= 626)%Z.
Proof. intros h Hh. unfold wpl_of. apply Z.div_le_upper_bound; lia. Qed.

Lemma wpl1_facts90 : forall w : Z, (1 <= w)%Z -> (1 <= wpl_of w 1)%Z /\ (w <= 32 * wpl_of w 1)%Z.
Proof.
  intros w Hw. unfold wpl_of.
  pose proof (Z.div_mod (w * 1 + 31) 32 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (w * 1 + 31) 32 ltac:(lia)) as B.
  split; lia.
Qed.

Lemma cellsZ_snoc : forall m l (a : Z) (v : word), cellsZ m l -> rdn SEGS m (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v) ->
  cellsZ m (l ++ [(a, v)]).
Proof.
  intros m l a v. induction l as [|[x y] t IH]; cbn [app cellsZ]; [tauto|].
  intros [H1 H2] H3. split; [exact H1 | exact (IH H2 H3)].
Qed.

Section Rot90W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Local Ltac jt_vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Lemma jt90cw_rd : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x1f768) 4 = Some (Z_to_le_bytes 4 490244).
Proof.
  intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1f768 4 HW) by (cbv [fst snd ll_ro LLU16]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite p16_segs. jt_vm_refl.
Qed.

Lemma jt90cc_rd : forall C A m md, W C A m md -> rdn SEGS m (Z_to_bv 64 0x1f6e8) 4 = Some (Z_to_le_bytes 4 491364).
Proof.
  intros C A m md HW. rewrite <- p16_segs. rewrite (W_rdn_ro C A m md 0x1f6e8 4 HW) by (cbv [fst snd ll_ro LLU16]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia).
  rewrite p16_segs. jt_vm_refl.
Qed.

Definition R90_STACK : Z := 192 + 112 + LSF.

Definition TK90 (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s w h : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z) : Prop :=
  forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd h w 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pix - RK_cmapcopy) (bR - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S.

Lemma r90_post_W : forall C A A2 m md M5 m6 vm2 regs r6 (s pixd cd data w h : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TK90 C A m md regs s w h cv ret S kR bR ->
  aroom A2 vm2 (kR - RK_pix - RK_cmapcopy) (bR - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy) ->
  (c_top C - LSTK + R90_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A2 m6 (with_vmmaps vm2 md) -> POSTM C A s m M5 -> POSTM C A s M5 m6 -> sub_live A A2 ->
  (forall a : word, ~ (data <= u a < data + 4 * wpl_of h 1 * w)%Z -> ~ (s - 192 <= u a < s - 136)%Z -> m6 a = M5 a) ->
  cellsZ M5 (R90C s ret regs ++ [((s - 128)%Z, Z_to_bv 64 pixd)]) ->
  getr r6 2 = Z_to_bv 64 (s - 192) -> (forall x, In x [3; 4]%list -> getr r6 x = getr regs x) ->
  (4096 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> (pixd mod 16 = 0)%Z ->
  (4096 <= data)%Z -> (data + 4 * (wpl_of h 1 * w) <= alloc_top (c_vm C))%Z -> (data mod 16 = 0)%Z -> pixd <> data ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of h 1 * w))%Z ->
  PIXat M5 pixd (hdv h w 1 cd data) -> cmres C A A2 M5 pixd data cd cv ->
  realizes SEGS (mkCfg (mkst r6 (0x98a2c : word) m6 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros C A A2 m md M5 m6 vm2 regs r6 s pixd cd data w h cv ret S kR bR CK HK Hrm Hlo Hhi Hret H2 HW6 PM5 PM6 SUB FT CE R2 RR
         Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d L2p L2d PXd CMR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold R90_STACK, LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  pose proof PXd as (_ & _ & WFd & _). pose proof (wf_data _ WFd) as Hd64. pose proof (wf_wpl _ WFd) as Hwp0. pose proof (wf_h _ WFd) as Hw0.
  cbn [p_data p_wpl p_h hdv] in Hd64, Hwp0, Hw0.
  assert (HP : (0 <= 4 * (wpl_of h 1 * w))%Z) by nia.
  assert (NEb : Z_to_bv 64 pixd <> Z_to_bv 64 data) by (apply zbv_ne2; lia).
  pose proof (V23LeptCmap2.blk_apart C A2 m6 _ _ _ _ _ CK HW6 L2p L2d NEb ltac:(lia) ltac:(lia)) as APpd. rewrite !u_Z2bv in APpd by lia.
  assert (CE6 : cellsZ m6 (R90C s ret regs ++ [((s - 128)%Z, Z_to_bv 64 pixd)])).
  { apply (cellsZ_keep M5 m6); [| exact CE]. unfold R90C. cbn [app].
    repeat constructor; cbn [fst]; try lia. all: intros x Hx; apply FT; lia. }
  unfold R90C in CE6. cbn [app] in CE6.
  destruct (r90_E al_rom r6 m6 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
              (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (Z_to_bv 64 pixd) ltac:(lia) Hs64 Hret CE6 R2)
    as (r7 & RUN7 & Z2 & Z1 & Z10 & Z8 & Z9 & Z18 & Z19 & Z20 & Z21 & Z22 & Z23 & Z24 & Z25 & Z26 & Z27 & AG7).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact RUN7 |].
  apply (HK A2 m6 vm2 r7 HW6).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM5 | exact PM6].
  - right. exists pixd, cd, data. split; [rewrite Z10; reflexivity |].
    unfold pixt_new. do 13 (split; [assumption|]). split.
    + apply (PIXat_frame M5); [exact PXd|]. intros x Hx. apply FT; lia.
    + apply (O23LeptRot90W.r90_cmres_frame C A A2 M5 m6 pixd data cd cv CMR ltac:(lia) ltac:(lia)).
      intros q k i Lq N1 N2 Hi.
      destruct (blk_range C A2 m6 _ q k CK HW6 Lq ltac:(lia)) as [Gq TOPq].
      pose proof (V23LeptCmap2.blk_apart C A2 m6 _ q (Z_to_bv 64 data) k (4 * (wpl_of h 1 * w)) CK HW6 Lq L2d N2 ltac:(lia) ltac:(lia)) as APq.
      rewrite u_Z2bv in APq by lia.
      apply FT; unfold at_; rewrite u_Z2bv by lia; lia.
  - exact Hrm.
Qed.

Lemma r90_tail_W : forall C A A2 m md m4 vm2 regs r4 (s pixs rc w h cm datas dir pixd cd data : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z),
  Cok C -> TK90 C A m md regs s w h cv ret S kR bR ->
  aroom A2 vm2 (kR - RK_pix - RK_cmapcopy) (bR - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy) ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + R90_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  (dir = 1 \/ dir = -1)%Z ->
  W C A2 m4 (with_vmmaps vm2 md) -> POSTM C A s m m4 -> sub_live A A2 ->
  cellsZ m4 (R90C s ret regs ++ [((s - 128)%Z, Z_to_bv 64 pixd)]) ->
  rdn SEGS m4 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w)) ->
  rdn SEGS m4 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h)) ->
  rdn SEGS m4 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
  getr r4 2 = Z_to_bv 64 (s - 192) -> getr r4 9 = Z_to_bv 64 pixs -> getr r4 19 = Z_to_bv 64 dir ->
  (forall x, In x [3; 4]%list -> getr r4 x = getr regs x) ->
  PIXat m4 pixs (hdvr rc w h 1 cm datas) -> live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (w <= 20000)%Z -> (h <= 20000)%Z -> (4 * (wpl_of w 1 * h) <= 67108864)%Z -> (4 * (wpl_of h 1 * w) <= 67108864)%Z -> (1 <= w)%Z -> (1 <= h)%Z ->
  (4096 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> (pixd mod 16 = 0)%Z ->
  (4096 <= data)%Z -> (data + 4 * (wpl_of h 1 * w) <= alloc_top (c_vm C))%Z -> (data mod 16 = 0)%Z -> pixd <> data ->
  live A (Z_to_bv 64 pixd) = None -> live A (Z_to_bv 64 data) = None ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  live A2 (Z_to_bv 64 pixd) = Some 64%Z -> live A2 (Z_to_bv 64 data) = Some (4 * (wpl_of h 1 * w))%Z ->
  PIXat m4 pixd (hdv h w 1 cd data) -> cmres C A A2 m4 pixd data cd cv ->
  realizes SEGS (mkCfg (mkst r4 (0x971e0 : word) m4 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros C A A2 m md m4 vm2 regs r4 s pixs rc w h cm datas dir pixd cd data cv ret S kR bR CK HK Hrm Hs16 Hlo Hhi Hret H2 Hdir HW4 PM4 SUB
         CE R112 R108 R116 Y2 Y9 Y19 RR PXs Lps Lds Hw2 Hh2 Hsz Hszd Hw Hh
         Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d L2p L2d PXd CMR.
  pose proof Hlo as Hlo0.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold R90_STACK, LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  destruct (wpl1_facts90 w Hw) as [Hwpw1 Hwpw32]. destruct (wpl1_facts90 h Hh) as [Hwph1 Hwph32].
  pose proof (O23LeptRot90W.wpl1_le w Hw) as Hwplw. pose proof (O23LeptRot90W.wpl1_le h Hh) as Hwplh.
  pose proof (wpl1_626 h ltac:(lia)) as Hwpl626.
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  pose proof (SUB _ _ Lps) as Lps2. pose proof (SUB _ _ Lds) as Lds2.
  destruct (blk_range C A2 m4 _ (Z_to_bv 64 pixs) 64 CK HW4 Lps2 ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  destruct (blk_range C A2 m4 _ (Z_to_bv 64 datas) (4 * (wpl_of w 1 * h)) CK HW4 Lds2 ltac:(nia)) as [Gds TOPds].
  pose proof (ai_live_hull A2 m4 _ _ _ (w_inv _ _ _ _ HW4) Lps2) as (_ & ALps & _).
  pose proof (ai_live_hull A2 m4 _ _ _ (w_inv _ _ _ _ HW4) Lds2) as (_ & ALds & _).
  assert (Hds64 : (0 <= datas < 2 ^ 64)%Z) by (pose proof (wf_data _ WFs) as Hd0; cbn [p_data hdvr] in Hd0; lia).
  rewrite u_Z2bv in Gds, TOPds, ALds, ALps by lia.
  assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
  pose proof (V23LeptCmap2.blk_apart C A2 m4 _ _ _ _ _ CK HW4 Lps2 L2p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
  assert (CE4 := CE). unfold R90C in CE. cbn [app cellsZ] in CE.
  destruct CE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RPD & _).
  set (M5 := MR90_D m4 s pixd data).
  assert (OUT5 : forall x : word, ~ (pixd + 12 <= u x < pixd + 36)%Z -> ~ (s - 136 <= u x < s - 128)%Z -> M5 x = m4 x).
  { intros x Hx1 Hx2. pose proof (u64_range x) as Ux. subst M5. unfold MR90_D, O23LeptRot90.MR90_C.
    rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (WP5 : W C A2 M5 (with_vmmaps vm2 md) /\ POSTM C A s m M5).
  { subst M5. unfold MR90_D, O23LeptRot90.MR90_C.
    apply (WP_win C A2 A m _ _ (Z_to_bv 64 (s - 136)) _ s CK); [| exact SUB | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
    do 3 (apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pixd) _ 64); [exact CK | | exact L2p | exact L0p | exact L00p | exact SUB | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
    split; [exact HW4 | exact PM4]. }
  destruct WP5 as [HW5 PM5].
  assert (PXd5 : PIXat M5 pixd (hdv h w 1 cd data)).
  { subst M5. unfold MR90_D.
    apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    unfold O23LeptRot90.MR90_C.
    exact (O23LeptRot90.r90_wr_spp_same _ pixd (hdv h w 1 cd data)
             (O23LeptRot90.r90_wr_fmt0 _ pixd (hdv h w 1 cd data)
                (O23LeptRot90.r90_wr_res0 m4 pixd (hdv h w 1 cd data) PXd eq_refl eq_refl) eq_refl)). }
  assert (RWD5 : rdn SEGS M5 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { subst M5. unfold MR90_D, O23LeptRot90.MR90_C. repeat rdn_peel1. exact R108. }
  assert (RHD5 : rdn SEGS M5 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))).
  { subst M5. unfold MR90_D, O23LeptRot90.MR90_C. repeat rdn_peel1. exact R112. }
  assert (RDD5 : rdn SEGS M5 (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 data))).
  { subst M5. unfold MR90_D. apply SeqExec.rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
  assert (CE5 : cellsZ M5 (R90C s ret regs ++ [((s - 128)%Z, Z_to_bv 64 pixd)])).
  { apply (cellsZ_keep m4 M5); [| exact CE4]. unfold R90C. cbn [app].
    repeat constructor; cbn [fst]; try lia. all: intros x Hx; apply OUT5; lia. }
  assert (CMR5 : cmres C A A2 M5 pixd data cd cv).
  { apply (O23LeptRot90W.r90_cmres_frame C A A2 m4 M5 pixd data cd cv CMR ltac:(lia) ltac:(lia)).
    intros q k i Lq N1 N2 Hi.
    destruct (blk_range C A2 m4 _ q k CK HW4 Lq ltac:(lia)) as [Gq TOPq].
    pose proof (V23LeptCmap2.blk_apart C A2 m4 _ q (Z_to_bv 64 pixd) k 64 CK HW4 Lq L2p N1 ltac:(lia) ltac:(lia)) as APq.
    rewrite u_Z2bv in APq by lia.
    apply OUT5; unfold at_; rewrite u_Z2bv by lia; lia. }
  assert (SOKd : store_ok SEGS m4 (Z_to_bv 64 pixd) 64 = true) by exact (V23LeptCmap2.blk_sok C A2 m4 _ pixd 64 CK HW4 L2p ltac:(lia) ltac:(lia) ltac:(lia)).
  assert (SOK136 : store_ok SEGS m4 (Z_to_bv 64 (s - 136)) 8 = true) by exact (W_sok_win C A2 m4 _ (s - 136) 8 CK HW4 ltac:(lia) ltac:(cbn; lia)).
  destruct Hdir as [-> | ->].
  - destruct (r90_Cw al_rom r4 m4 s pixd pixs (hdv h w 1 cd data) (hdvr rc w h 1 cm datas) ltac:(lia) Hs64 ltac:(lia) ltac:(lia) ltac:(lia)
                (al16_mod8 _ ALp) (al16_mod8 _ ALps) ltac:(lia) ltac:(lia) ltac:(lia) PXd PXs eq_refl eq_refl eq_refl ltac:(reflexivity)
                eq_refl eq_refl eq_refl ltac:(reflexivity) SOKd SOK136 RPD R116 (jt90cw_rd C A2 M5 _ HW5) Y2 Y9 Y19)
      as (r5 & RUN5 & Z2 & Z10 & Z8 & Z18 & Z9 & Z19 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
    apply (V23LeptRot90cwW.cw_arm_W C A A2 (with_vmmaps vm2 md) M5 s data (wpl_of h 1) w h (4 * (wpl_of h 1 * w)) datas (wpl_of w 1) (4 * (wpl_of w 1 * h)) S
             CK SUB L2d ltac:(lia) L0d L00d Lds2 ltac:(lia) ltac:(lia) Hds64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(lia) Hs64 ltac:(lia) RWD5 RHD5 RDD5 ALd ALds ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hhi r5 HW5 Z2 Z10 Z8 Z18).
    intros m6 r6 HW6 PM6 FT6 AG6.
    apply (r90_post_W C A A2 m md M5 m6 vm2 regs r6 s pixd cd data w h cv ret S kR bR CK HK Hrm Hlo0 Hhi Hret H2 HW6 PM5 PM6 SUB FT6 CE5
             ltac:(csr; reflexivity) ltac:(intros x Hx; destruct Hx as [<- | [<- | []]]; csr; reflexivity) Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d L2p L2d PXd5 CMR5).
  - destruct (r90_Cc al_rom r4 m4 s pixd pixs (hdv h w 1 cd data) (hdvr rc w h 1 cm datas) ltac:(lia) Hs64 ltac:(lia) ltac:(lia) ltac:(lia)
                (al16_mod8 _ ALp) (al16_mod8 _ ALps) ltac:(lia) ltac:(lia) ltac:(lia) PXd PXs eq_refl eq_refl eq_refl ltac:(reflexivity)
                eq_refl eq_refl eq_refl ltac:(reflexivity) SOKd SOK136 RPD R116 (jt90cc_rd C A2 M5 _ HW5) Y2 Y9 Y19)
      as (r5 & RUN5 & Z2 & Z10 & Z8 & Z18 & Z9 & Z19 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
    apply (V23LeptRot90ccwW.cc_arm_W C A A2 (with_vmmaps vm2 md) M5 s data (wpl_of h 1) w h (4 * (wpl_of h 1 * w)) datas (wpl_of w 1) (4 * (wpl_of w 1 * h)) S
             CK SUB L2d ltac:(lia) L0d L00d Lds2 ltac:(lia) ltac:(lia) Hds64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
             ltac:(lia) Hs64 ltac:(lia) RWD5 RHD5 RDD5 ALd ALds ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hhi ltac:(lia) ltac:(lia) r5 HW5 Z2 Z10 Z8 Z18).
    intros m6 r6 HW6 PM6 FT6 AG6.
    apply (r90_post_W C A A2 m md M5 m6 vm2 regs r6 s pixd cd data w h cv ret S kR bR CK HK Hrm Hlo0 Hhi Hret H2 HW6 PM5 PM6 SUB FT6 CE5
             ltac:(csr; reflexivity) ltac:(intros x Hx; destruct Hx as [<- | [<- | []]]; csr; reflexivity) Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d L2p L2d PXd5 CMR5).
Qed.

Theorem pixRotate90_W : forall C A m md regs (s pixs rc w h cm datas dir : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + R90_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 dir -> (dir = 1 \/ dir = -1)%Z ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix + RK_cmapcopy <= kR)%Z ->
  (RB_pixT (4 * (wpl_of h 1 * w)) + RB_cmapcopy <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd h w 1 cd data cv) ) ->
     aroom A' vm' (kR - RK_pix - RK_cmapcopy) (bR - RB_pixT (4 * (wpl_of h 1 * w)) - RB_cmapcopy) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x9713c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s pixs rc w h cm datas dir cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 Hdir PXs HOK Hw Hh Lps Lds HCM kR bR Hrm Hrk Hrb HK.
  assert (HK90 : TK90 C A m md regs s w h cv ret S kR bR) by exact HK.
  pose proof Hlo as Hlo0.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold R90_STACK, LSF in Hlo.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (Hs64 : (s < 2 ^ 64)%Z) by lia.
  assert (RKc : (0 <= RK_cmapcopy)%Z) by (unfold RK_cmapcopy; lia).
  assert (RBc : (0 <= RB_cmapcopy)%Z) by (unfold RB_cmapcopy; lia).
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof PXs as (Hs0 & Hs64' & WFs & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lps ltac:(lia)) as [Gps TOPps]. rewrite u_Z2bv in Gps, TOPps by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lps) as (_ & ALps & _). rewrite u_Z2bv in ALps by lia.
  destruct (r90_A al_rom regs m s pixs dir (hdvr rc w h 1 cm datas) ret ltac:(lia) Hs64 Hs16 ltac:(lia) (al16_mod8 _ ALps) PXs ltac:(lia) eq_refl
              ltac:(cbn [p_w hdvr]; lia) ltac:(cbn [p_h hdvr]; lia) Hdir
              (W_sok_win C A m md (s - 192) 192 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & Q19 & AG1).
  cbn [p_w p_h p_d hdvr] in Q10, Q11.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (MR90_A m s (hdvr rc w h 1 cm datas) ret regs) md /\ POSTM C A s m (MR90_A m s (hdvr rc w h 1 cm datas) ret regs))
    by (unfold MR90_A, DIM90, FR90; cbn [p_w p_h p_d hdvr]; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 192 <= u x < s)%Z -> MR90_A m s (hdvr rc w h 1 cm datas) ret regs x = m x).
  { intros x Hx. unfold MR90_A, DIM90, FR90. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (CE1 : cellsZ (MR90_A m s (hdvr rc w h 1 cm datas) ret regs) (R90C s ret regs)).
  { unfold MR90_A, DIM90, FR90, R90C. cbn [cellsZ p_w p_h p_d hdvr]. repeat split; rdn_solve. }
  assert (R112 : rdn SEGS (MR90_A m s (hdvr rc w h 1 cm datas) ret regs) (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))).
  { unfold MR90_A, DIM90. cbn [p_w p_h p_d hdvr]. rdn_peel1. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (R108 : rdn SEGS (MR90_A m s (hdvr rc w h 1 cm datas) ret regs) (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))).
  { unfold MR90_A, DIM90. cbn [p_w p_h p_d hdvr]. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (R116 : rdn SEGS (MR90_A m s (hdvr rc w h 1 cm datas) ret regs) (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))).
  { unfold MR90_A, DIM90. cbn [p_w p_h p_d hdvr]. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  set (M1 := MR90_A m s (hdvr rc w h 1 cm datas) ret regs) in *.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  apply (V23LeptPixCreateT2.pixCreate_szT2_W C A M1 md r1 (s - 192) h w 1 (Z_to_bv 64 0x971d0) S CK HW1 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12
           ltac:(lia) ltac:(lia) ltac:(nia) ltac:(lia)).
  intros A1 m2 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x971d0) with (0x971d0 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (CE2 : cellsZ m2 (R90C s ret regs)).
  { apply (cellsZ_frm C (s - 192) M1 m2 _ CK (proj1 PMa) ltac:(lia)); [| exact CE1]. unfold R90C. repeat constructor; cbn [fst]; lia. }
  assert (F2 : forall (a : Z) (n : nat), (s - 192 <= a)%Z -> (a + Z.of_nat n <= 2 ^ 64)%Z -> rdn SEGS m2 (Z_to_bv 64 a) n = rdn SEGS M1 (Z_to_bv 64 a) n).
  { intros a n Ha Hn. exact (FRM_rdn16 C (s - 192) M1 m2 a n CK (proj1 PMa) Ha Hn ltac:(lia)). }
  assert (R112b : rdn SEGS m2 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))) by (rewrite F2 by (cbn; lia); exact R112).
  assert (R108b : rdn SEGS m2 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (rewrite F2 by (cbn; lia); exact R108).
  assert (R116b : rdn SEGS m2 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))) by (rewrite F2 by (cbn; lia); exact R116).
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 192)) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pixd & data & Hres & HOKd & PN)].
  - assert (SUBa : sub_live A A1) by (apply sub_live_eq; exact LIVEQ).
    destruct (r90_N al_rom r2 m2 s ltac:(lia) Hs64 (W_sok_win C A1 m2 _ (s - 128) 8 CK HWa ltac:(lia) ltac:(cbn; lia))
                ltac:(rdn_peel1; exact (W_sev_got C A1 m2 _ HWa)) ltac:(rdn_peel1; exact (W_sev C A1 m2 _ HWa)) E2 Hres0)
      as (r3 & RUN3 & V1 & V10 & V11 & V12 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (M3 := wbytes m2 (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 0))) in *.
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3) by (subst M3; wp_win CK).
    destruct WP3 as [HW3 PM3].
    assert (R3_2 : getr r3 2 = Z_to_bv 64 (s - 192)) by (csr; reflexivity).
    apply (V23LeptErr.returnErrorPtr_W C A1 M3 _ r3 (s - 192) 0x126da 0x193f3 13 11 (Z_to_bv 64 0x97a50) (Z_to_bv 64 0) S CK HW3 R3_2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) V1 ltac:(red; apply bv_eq; reflexivity)
             V10 V11 V12 str_r90_pixd str_r90).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    replace (Z_to_bv 64 0x97a50) with (0x97a50 : word) by (apply bv_eq; reflexivity).
    assert (CE4 : cellsZ m4 (R90C s ret regs)).
    { apply (cellsZ_out M3 m4 (s - 192 - (16 + 3376)) (s - 192)); [exact OUT4 | unfold R90C; repeat constructor; cbn [fst]; lia |].
      apply (cellsZ_out m2 M3 (s - 128) (s - 120)); [| unfold R90C; repeat constructor; cbn [fst]; lia | exact CE2].
      intros x Hx. subst M3. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    unfold R90C in CE4.
    destruct (r90_NE al_rom r5 m4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) ltac:(lia) Hs64 Hret CE4 ltac:(csr; reflexivity))
      as (r6 & RUN6 & W2 & W1 & W10 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN6 |].
    apply (HK A1 m4 vm1 r6).
    + exact HW4.
    + apply cs_kept_intro; csr; reflexivity.
    + eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C A A1 s M3 m4 SUBa).
      eapply (POSTM_range C A1 M3 _ m4); [exact CK | exact HW3 | exact OUT4 | lia | lia | lia].
    + left. split; [rewrite W10; exact A10 | exact LIVEQ].
    + apply (aroom_mono _ _ (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of h 1 * w)))); [apply HRTa; [exact Hrm | lia | lia] | lia | lia].
  - destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & LEQ & PXd & _).
    cbn [p_wpl p_h set_data O23LeptPixHdrT2.pix_hdr] in TOPd, L1d.
    change (PIXat m2 pixd (hdv h w 1 0 data)) in PXd.
    destruct HOKd as (_ & _ & _ & Hszd).
    assert (NEsp : Z_to_bv 64 pixs <> Z_to_bv 64 pixd) by (intros E; rewrite E in Lps; rewrite Lps in L0p; discriminate).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new2; [exact L0p | exact L0d | exact L1p | exact L1d | exact LEQ]).
    pose proof (SUBa _ _ Lps) as Lps1.
    pose proof (V23LeptCmap2.blk_apart C A1 m2 _ _ _ _ _ CK HWa Lps1 L1p NEsp ltac:(lia) ltac:(lia)) as APsp. rewrite !u_Z2bv in APsp by lia.
    destruct (r90_B al_rom r2 m2 s pixd ltac:(lia) Hs64 ltac:(lia) (W_sok_win C A1 m2 _ (s - 128) 8 CK HWa ltac:(lia) ltac:(cbn; lia)) E2 Hres)
      as (r3 & RUN3 & X1 & X10 & X11 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    set (M3 := wbytes m2 (Z_to_bv 64 (s - 128)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) in *.
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3) by (subst M3; wp_win CK).
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (s - 128 <= u x < s - 120)%Z -> M3 x = m2 x).
    { intros x Hx. subst M3. rewrite wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PXd3 : PIXat M3 pixd (hdv h w 1 0 data)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; apply OUT3; lia]).
    assert (PXs2 : PIXat m2 pixs (hdvr rc w h 1 cm datas)).
    { apply (PIXat_frame m); [exact PXs|]. intros x Hx.
      rewrite (O23LeptCmap2.LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lps ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    assert (PXs3 : PIXat M3 pixs (hdvr rc w h 1 cm datas)) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; apply OUT3; lia]).
    assert (HCM3 : cm = 0%Z \/ (CMAPat M3 cm cv /\ cmap_ok cv /\ live A1 (Z_to_bv 64 cm) = Some 24%Z /\ live A1 (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)).
    { destruct HCM as [CM0 | (CM & CMOK & Lcm & Larr)]; [left; exact CM0 | right].
      pose proof CM as (Hc0 & Hc64 & _).
      destruct (blk_range C A m md (Z_to_bv 64 cm) 24 CK HW Lcm ltac:(lia)) as [Gcm TOPcm]. rewrite u_Z2bv in Gcm, TOPcm by lia.
      split; [| split; [exact CMOK | split; [exact (SUBa _ _ Lcm) | exact (SUBa _ _ Larr)]]].
      apply (CMAPat_frame m); [exact CM|]. intros x Hx. rewrite OUT3 by lia.
      rewrite (O23LeptCmap2.LIVK_at A M1 m2 cm 24 x (proj2 PMa) Lcm ltac:(lia) ltac:(lia) Hx). apply OUT1. lia. }
    assert (X2 : getr r3 2 = Z_to_bv 64 (s - 192)) by (csr; reflexivity).
    assert (X4 : getr r3 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (X11' : getr r3 11 = Z_to_bv 64 pixs) by (rewrite X11; csr; reflexivity).
    apply (V23LeptPixCopyA.pixCopyColormap_W C A A1 M3 _ r3 (s - 192) pixd pixs (hdv h w 1 0 data) (hdvr rc w h 1 cm datas) cv (Z_to_bv 64 0x971e0) S CK HW3 SUBa X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11'
             PXd3 PXs3 eq_refl eq_refl ltac:(lia) L1p L0p L00p Lps1 HCM3
             (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of h 1 * w))) ltac:(rewrite with_vmmaps_vmmaps; apply HRTa; [exact Hrm | lia | lia]) ltac:(lia) ltac:(lia)).
    intros A2 m4 vm2 r4 HWb CSb PMb OUTb Hrm2. rewrite with_vmmaps_twice in HWb |- *.
    replace (Z_to_bv 64 0x971e0) with (0x971e0 : word) by (apply bv_eq; reflexivity).
    assert (PMb' : POSTM C A s m m4) by (eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PMb]; lia]).
    assert (CE3 : cellsZ M3 (R90C s ret regs ++ [((s - 128)%Z, Z_to_bv 64 pixd)])).
    { apply cellsZ_snoc.
      - apply (cellsZ_out m2 M3 (s - 128) (s - 120)); [exact OUT3 | unfold R90C; repeat constructor; cbn [fst]; lia | exact CE2].
      - subst M3. apply SeqExec.rdn_wbytes_hit8. rewrite u_Z2bv by lia. lia. }
    assert (CE4 : cellsZ m4 (R90C s ret regs ++ [((s - 128)%Z, Z_to_bv 64 pixd)])).
    { apply (cellsZ_frm C (s - 192) M3 m4 _ CK (proj1 PMb) ltac:(lia)); [| exact CE3]. unfold R90C. cbn [app]. repeat constructor; cbn [fst]; lia. }
    assert (FR4 : forall (a : Z) (n : nat), (s - 120 <= a)%Z -> (a + Z.of_nat n <= s)%Z -> rdn SEGS m4 (Z_to_bv 64 a) n = rdn SEGS m2 (Z_to_bv 64 a) n).
    { intros a n Ha Hn. rewrite (FRM_rdn16 C (s - 192) M3 m4 a n CK (proj1 PMb)) by lia. subst M3. rdn_peel1. reflexivity. }
    assert (R112c : rdn SEGS m4 (Z_to_bv 64 (s - 112)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 w))) by (rewrite FR4 by (cbn; lia); exact R112b).
    assert (R108c : rdn SEGS m4 (Z_to_bv 64 (s - 108)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 h))) by (rewrite FR4 by (cbn; lia); exact R108b).
    assert (R116c : rdn SEGS m4 (Z_to_bv 64 (s - 116)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1))) by (rewrite FR4 by (cbn; lia); exact R116b).
    assert (Y2 : getr r4 2 = Z_to_bv 64 (s - 192)) by (csr; reflexivity).
    assert (Y9 : getr r4 9 = Z_to_bv 64 pixs) by (csr; reflexivity).
    assert (Y19 : getr r4 19 = Z_to_bv 64 dir) by (csr; reflexivity).
    assert (RR : forall x, In x [3; 4]%list -> getr r4 x = getr regs x) by (intros x Hx; destruct Hx as [<- | [<- | []]]; csr; reflexivity).
    assert (PXs4 : PIXat m4 pixs (hdvr rc w h 1 cm datas)).
    { apply (PIXat_frame M3); [exact PXs3|]. intros x Hx. exact (O23LeptCmap2.LIVK_at A M3 m4 pixs 64 x (proj2 PMb) Lps ltac:(lia) ltac:(lia) Hx). }
    destruct OUTb as [[LIVEQ PXd4] | (cd & ad & CC & PXd4)].
    + apply (r90_tail_W C A A2 m md m4 vm2 regs r4 s pixs rc w h cm datas dir pixd 0 data cv ret S kR bR CK HK90 Hrm2 Hs16 Hlo0 Hhi Hret H2 Hdir
               HWb PMb' (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) CE4 R112c R108c R116c Y2 Y9 Y19 RR PXs4 Lps Lds
               Hw2 Hh2 Hsz Hszd Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               ltac:(rewrite LIVEQ; exact L1p) ltac:(rewrite LIVEQ; exact L1d) PXd4).
      left. split; [reflexivity|]. intros q N1 N2. rewrite LIVEQ. apply LEQ; assumption.
    + pose proof CC as (CMOKc & Gcd & TOPcd & ALcd & Gad & TOPad & ALad & NEcdad & LA1cd & LA1ad & L00cd & L00ad & L2cd & L2ad & LEQ2 & CM4).
      assert (NEcdp : Z_to_bv 64 cd <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1cd; rewrite L1p in LA1cd; discriminate).
      assert (NEadp : Z_to_bv 64 ad <> Z_to_bv 64 pixd) by (intros E; rewrite E in LA1ad; rewrite L1p in LA1ad; discriminate).
      assert (NEcdd : Z_to_bv 64 cd <> Z_to_bv 64 data) by (intros E; rewrite E in LA1cd; rewrite L1d in LA1cd; discriminate).
      assert (NEadd : Z_to_bv 64 ad <> Z_to_bv 64 data) by (intros E; rewrite E in LA1ad; rewrite L1d in LA1ad; discriminate).
      assert (SUBb : sub_live A1 A2) by (eapply sub_live_new2; [exact LA1cd | exact LA1ad | exact L2cd | exact L2ad | exact LEQ2]).
      apply (r90_tail_W C A A2 m md m4 vm2 regs r4 s pixs rc w h cm datas dir pixd cd data cv ret S kR bR CK HK90 Hrm2 Hs16 Hlo0 Hhi Hret H2 Hdir
               HWb PMb' (sub_live_trans _ _ _ SUBa SUBb) CE4 R112c R108c R116c Y2 Y9 Y19 RR PXs4 Lps Lds
               Hw2 Hh2 Hsz Hszd Hw Hh Gp TOPp ALp Gd TOPd ALd NEpd L0p L0d L00p L00d
               (SUBb _ _ L1p) (SUBb _ _ L1d) PXd4).
      right. exists ad.
      split; [exact CMOKc|]. split; [exact Gcd|]. split; [exact TOPcd|]. split; [exact Gad|]. split; [exact TOPad|]. split; [exact NEcdad|].
      split; [intros E; apply NEcdp; rewrite E; reflexivity|]. split; [intros E; apply NEcdd; rewrite E; reflexivity|].
      split; [intros E; apply NEadp; rewrite E; reflexivity|]. split; [intros E; apply NEadd; rewrite E; reflexivity|].
      split; [rewrite <- (LEQ _ NEcdp NEcdd); exact LA1cd|]. split; [rewrite <- (LEQ _ NEadp NEadd); exact LA1ad|].
      split; [exact L00cd|]. split; [exact L00ad|]. split; [exact L2cd|]. split; [exact L2ad|]. split; [exact CM4|].
      intros q N1 N2 N3 N4. rewrite (LEQ2 q N3 N4). apply LEQ; assumption.
Qed.

End Rot90W.
