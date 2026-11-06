(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21LeptStderr V21LeptBase V21LeptUb.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21CL7a.
Import V21CL7a.V21LeptErr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21CL8a.
Import V21CL8a.V21LeptPixHdr.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21LeptCmapValid V21LeptBox V21LeptCmap2 V21LeptPixCopy V21LeptSelLoop V21LeptSelSegs.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_pixs_not_defined : str16 0x10298 16. Proof. str16_tac. Qed.
Lemma str_no_colormap : str16 0x108f0 11. Proof. str16_tac. Qed.
Lemma str_sindex : str16 0x10368 31. Proof. str16_tac. Qed.
Lemma str_depth : str16 0x10891 22. Proof. str16_tac. Qed.
Lemma str_adding : str16 0x10c63 23. Proof. str16_tac. Qed.
Lemma str_pixSetSelectCmap : str16 0x10d41 16. Proof. str16_tac. Qed.
Lemma str_no_free : str16 0x10b69 21. Proof. str16_tac. Qed.
Lemma str_pixcmapAddColor : str16 0x10abb 15. Proof. str16_tac. Qed.

Lemma err_msg_str : forall pc msg, In (pc, msg) [(0x1699c, 0x10298); (0x169c4, 0x108f0); (0x169ec, 0x10368); (0x16a14, 0x10891)]%Z ->
  exists k, str16 msg k.
Proof.
  intros pc msg Hin. cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as _ <-;
    [exists 16%Z; exact str_pixs_not_defined | exists 11%Z; exact str_no_colormap | exists 31%Z; exact str_sindex | exists 22%Z; exact str_depth].
Qed.

Lemma cset_n_self : forall m c cv, CMAPat m c cv -> CMAPat m c (cset_n cv (c_n cv)).
Proof. intros m c cv H. destruct cv. exact H. Qed.

(* [comment removed for export] *)
Lemma rdn4_1 : forall segs m (a : word) bs, rdn segs m a 4 = Some bs -> exists b, rdn segs m a 1 = Some [b].
Proof.
  intros segs m a bs R. cbn [rdn] in R. cbn [rdn]. destruct (m a) as [b|]; [| destruct (seg_rom segs a); [|discriminate]].
  - exists b. reflexivity.
  - eexists. reflexivity.
Qed.

Section SelCmap.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU21} {P16 : V21Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition SK (C : lctx) (Ar A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s pixd bx w h d cd data : Z) (cv : cmapv) (ret : word) (S : TSet) : Prop :=
  forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     PIXat m' pixd (hdv w h d cd data) ->
     (cd <> 0%Z -> exists n', (1 <= n' <= c_nalloc cv)%Z /\ CMAPat m' cd (cset_n cv n')) ->
     (bx <> 0%Z -> BOXat m' bx 278 35 122 50 1) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S.

#[local] Definition sc_rest : list (bv 5) := [3; 4]%bv.

(* [comment removed for export] *)
Lemma sel_err_W : forall C Ar A m md regs (s pixd bx w h d cd data : Z) (cv : cmapv) (ret : word) (S : TSet) M r (pc msg : Z),
  Cok C -> SK C Ar A m md regs s pixd bx w h d cd data cv ret S -> sub_live Ar A ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  In (pc, msg) [(0x1699c, 0x10298); (0x169c4, 0x108f0); (0x169ec, 0x10368); (0x16a14, 0x10891)]%Z ->
  W C A M md -> POSTM C Ar s m M -> cellsZ M (frame13 s ret (svr13 regs)) ->
  (1 <= pixd)%Z -> (pixd + 64 <= alloc_top (c_vm C))%Z -> PIXat M pixd (hdv w h d cd data) ->
  (cd <> 0%Z -> (1 <= cd)%Z /\ (cd + 24 <= alloc_top (c_vm C))%Z /\ exists n', (1 <= n' <= c_nalloc cv)%Z /\ CMAPat M cd (cset_n cv n')) ->
  (bx <> 0%Z -> (1 <= bx)%Z /\ (bx + 20 <= alloc_top (c_vm C))%Z /\ BOXat M bx 278 35 122 50 1) ->
  getr r 2 = Z_to_bv 64 (s - 144) -> (forall x, In x sc_rest -> getr r x = getr regs x) -> getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (Z_to_bv 64 pc) M al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd bx w h d cd data cv ret S M r pc msg CK HK SUB Hs16 Hlo Hhi Hret Hin HW PM CE Hp TOPp PX HCM HBX R2 RR H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. unfold LSF in *.
  destruct (err_msg_str pc msg Hin) as (k & Sk).
  destruct (ss_ehead al_rom pc msg r M s Hin (W_sev_got C A M md HW) (W_sev C A M md HW) R2) as (r1 & RUN1 & Q2 & Q10 & Q11 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct (ss_etail al_rom r1 M s ret (svr13 regs) msg ltac:(lia) ltac:(lia) CE Q2 Q10 Q11)
    as (r2 & RUN2 & P2 & P1 & P10 & P11 & P12 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  unfold svr13 in *.
  apply (returnErrorInt_W C A M md r2 s msg 0x10d41 k 16 ret (Z_to_bv 64 1) S CK HW P2 Hs16 ltac:(unfold LSF; lia) Hhi P1 Hret P10 P11 P12 Sk str_pixSetSelectCmap).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?P8, ?P9, ?P18, ?P19, ?P20, ?P21, ?P22, ?P23, ?P24, ?P25, ?P26, ?P27; try reflexivity.
    all: unfold sc_rest in RR; csr; reflexivity.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C Ar A _ _ _ SUB). eapply (POSTM_range C A M md m4); [exact CK | exact HW | exact OUT4 | lia | lia | lia].
  - apply (PIXat_frame M); [exact PX|]. intros x Hx. apply OUT4. lia.
  - intros NZ. destruct (HCM NZ) as (Hc1 & TOPc & n' & Hn' & CM). exists n'. split; [exact Hn'|]. apply (CMAPat_frame M); [exact CM|]. intros x Hx. apply OUT4. lia.
  - intros NZ. destruct (HBX NZ) as (Hb1 & TOPb & BX). apply (BOXat_frame M); [exact BX|]. intros x Hx. apply OUT4. lia.
Qed.

(* [comment removed for export] *)
Ltac rd4 v := rewrite <- (w2l_Z4 v) by lia; repeat (first [apply rdn_wbytes_hit4; rewrite ?u_Z2bv by lia; lia | rdn_peel1]).

(* [comment removed for export] *)
Lemma sel_loop_W : forall C Ar A m md regs (s pixd bx w h d cd data x1 x2 y1 y2 n' : Z) (cv : cmapv) (ibs : list byte) (ret : word) (S : TSet) M r,
  Cok C -> SK C Ar A m md regs s pixd bx w h d cd data cv ret S -> sub_live Ar A ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A M md -> POSTM C Ar s m M -> cellsZ M (frame13 s ret (svr13 regs)) ->
  PIXat M pixd (hdv w h d cd data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (1 <= cd)%Z -> CMAPat M cd (cset_n cv n') -> (1 <= n' <= c_nalloc cv)%Z -> live A (Z_to_bv 64 cd) = Some 24%Z ->
  Z_to_bv 64 pixd <> Z_to_bv 64 data -> Z_to_bv 64 cd <> Z_to_bv 64 data ->
  (bx <> 0%Z -> BOXat M bx 278 35 122 50 1 /\ live A (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data) ->
  (0 <= x1 < 2 ^ 31 - 1)%Z -> (0 <= x2 < 2 ^ 31 - 1)%Z -> (0 <= y1 < 2 ^ 31 - 1)%Z -> (0 <= y2 < 2 ^ 31 - 1)%Z ->
  rdn SEGS M (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS M (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS M (Z_to_bv 64 (s - 116)) 4 = Some (Z_to_le_bytes 4 x1) -> rdn SEGS M (Z_to_bv 64 (s - 120)) 4 = Some (Z_to_le_bytes 4 y1) ->
  rdn SEGS M (Z_to_bv 64 (s - 132)) 4 = Some ibs ->
  getr r 2 = Z_to_bv 64 (s - 144) -> getr r 10 = Z_to_bv 64 (wpl_of w d) -> getr r 8 = Z_to_bv 64 2 -> getr r 9 = Z_to_bv 64 d ->
  getr r 18 = Z_to_bv 64 data -> getr r 20 = Z_to_bv 64 x2 -> getr r 21 = Z_to_bv 64 y2 ->
  (forall x, In x sc_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x16b14 : word) M al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd bx w h d cd data x1 x2 y1 y2 n' cv ibs ret S M r CK HK SUB Hs16 Hlo Hhi Hret H2 HW PM CE PX HOK Hw Hh Hd
         Lp Ld LdA Ld0 Hcd CM Hn' Lc NEpd NEcd HBX Hx1 Hx2 Hy1 Hy2 Cw Ch Cx1 Cy1 Cidx R2 R10 R8 R9 R18 R20 R21 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof CM as (Hc0 & Hc64 & _). pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat.
  destruct (blk_range C A M md (Z_to_bv 64 pixd) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A M md (Z_to_bv 64 data) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A M md (Z_to_bv 64 cd) 24 CK HW Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  assert (Hlen : length ibs = 4%nat) by (exact (rdn_length _ _ _ _ _ Cidx)).
  destruct (rdn4_1 SEGS M _ ibs Cidx) as [ib Cidx1].
  assert (RAS0 : forall a : word, (data <= u a < data + 4 * (wpl_of w d * h))%Z -> M a <> None).
  { intros a Ha. destruct (blk_byte C A M md (Z_to_bv 64 data) _ a CK HW Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact D. }
  assert (Hdal : (data mod 4 = 0)%Z) by (clear - ALd Gd; rewrite <- (Z.add_0_r data); apply mod16_plus_mod4; [exact ALd | reflexivity]).
  destruct (sel_loop al_rom M data w h d (wpl_of w d) s x1 x2 y1 y2 2 ibs ib ltac:(lia) ltac:(lia) Hd ltac:(unfold wpl_of; reflexivity) Gd Hdal ltac:(lia)
              ltac:(lia) Hx1 Hx2 Hy1 Hy2 ltac:(lia) Cw Ch Cx1 Cy1 Cidx Hlen Cidx1 r M (RB_m0 M data h (wpl_of w d) RAS0) R2 R10 R8 R9 R18 R20 R21)
    as (r5 & m5 & RUN5 & RB5 & Q2 & Q10 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN5 |].
  destruct RB5 as [E5 D5]. unfold inras in E5, D5.
  assert (CH : forall a, m5 a <> M a -> scratch C s a \/ (exists p k, live A p = Some k /\ live Ar p = None /\ (u p <= u a < u p + k)%Z)).
  { intros a NE. right. exists (Z_to_bv 64 data), (4 * (wpl_of w d * h))%Z. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact LdA|]].
    destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply E5; lia|].
    destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w d * h))); [lia | exfalso; apply NE; apply E5; lia]. }
  assert (HW5 : W C A m5 md).
  { apply (W_local C A M md m5 s CK HW Hhi).
    - intros a NE. destruct (CH a NE) as [X|(p & k & L & _ & R)]; [left; exact X | right]. exists p, k. split; [exact L|]. split; [|exact R].
      destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact Ld0|]. exfalso. apply NE. apply E5.
      pose proof (blk_apart C A M md _ _ _ _ CK HW L Ld NE' ltac:(pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) L); lia) ltac:(lia)) as D. rewrite u_Z2bv in D by lia. lia.
    - intros a Da. destruct (Z_lt_ge_dec (u a) data); [rewrite E5 by lia; exact Da|]. destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w d * h))); [apply D5; lia | rewrite E5 by lia; exact Da]. }
  assert (PM5 : POSTM C Ar s m m5) by (eapply POSTM_trans; [exact PM | exact (POSTM_local C Ar A M md m5 s CK HW SUB CH)]).
  assert (EQ5 : forall (p k : Z) (x : word), live A (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 data -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z -> (p <= u x < p + k)%Z -> m5 x = M x).
  { intros p k x L NE' G0 K0 Hx. apply E5. pose proof (blk_apart C A M md _ _ _ _ CK HW L Ld NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
  assert (CE5 : cellsZ m5 (frame13 s ret (svr13 regs))) by (eapply (cells13_out M m5 data (data + 4 * (wpl_of w d * h))); [intros x Hx; apply E5; lia | lia | lia | lia | exact CE]).
  destruct (ss_RET al_rom r5 m5 s ret (svr13 regs) (Z_to_bv 64 0) ltac:(lia) ltac:(lia) Hret CE5 Q2 Q10)
    as (r6 & RUN6 & P2 & P1 & P10 & P8 & P9 & P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & AG6).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
  unfold svr13 in *.
  apply (HK m5 r6 HW5).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?P8, ?P9, ?P18, ?P19, ?P20, ?P21, ?P22, ?P23, ?P24, ?P25, ?P26, ?P27; try reflexivity.
    all: rewrite (AG5 _) by (unfold loop_clob; notin_list); unfold sc_rest in RR; csr; reflexivity.
  - exact PM5.
  - apply (PIXat_frame M); [exact PX|]. intros x Hx. exact (EQ5 pixd 64%Z x Lp NEpd ltac:(lia) ltac:(lia) Hx).
  - intros _. exists n'. split; [exact Hn'|]. apply (CMAPat_frame M); [exact CM|]. intros x Hx. exact (EQ5 cd 24%Z x Lc NEcd ltac:(lia) ltac:(lia) Hx).
  - intros NZ. destruct (HBX NZ) as (BX & Lb & NEbd). pose proof BX as (Hb1 & Hb64 & _).
    apply (BOXat_frame M); [exact BX|]. intros x Hx. exact (EQ5 bx 20%Z x Lb NEbd ltac:(lia) ltac:(lia) Hx).
Qed.

(* [comment removed for export] *)
Lemma sel_tail_W : forall C Ar A m md regs (s pixd bx w h d cd data n' : Z) (cv : cmapv) (ibs : list byte) (ret : word) (S : TSet) M r,
  Cok C -> SK C Ar A m md regs s pixd bx w h d cd data cv ret S -> sub_live Ar A ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret -> getr regs 2 = Z_to_bv 64 s ->
  W C A M md -> POSTM C Ar s m M -> cellsZ M (frame13 s ret (svr13 regs)) ->
  PIXat M pixd (hdv w h d cd data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (1 <= cd)%Z -> CMAPat M cd (cset_n cv n') -> (1 <= n' <= c_nalloc cv)%Z -> live A (Z_to_bv 64 cd) = Some 24%Z ->
  Z_to_bv 64 pixd <> Z_to_bv 64 data -> Z_to_bv 64 cd <> Z_to_bv 64 data ->
  (bx = 0%Z \/ (BOXat M bx 278 35 122 50 1 /\ live A (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data)) ->
  rdn SEGS M (Z_to_bv 64 (s - 132)) 4 = Some ibs ->
  getr r 2 = Z_to_bv 64 (s - 144) -> getr r 19 = Z_to_bv 64 pixd -> getr r 18 = Z_to_bv 64 bx -> getr r 8 = Z_to_bv 64 2 -> getr r 9 = Z_to_bv 64 d ->
  (forall x, In x sc_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (mkst r (0x16a7c : word) M al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd bx w h d cd data n' cv ibs ret S M r CK HK SUB Hs16 Hlo Hhi Hret H2 HW PM CE PX HOK Hw Hh Hd
         Lp Ld LdA Ld0 Hcd CM Hn' Lc NEpd NEcd HBX Cidx R2 R19 R18 R8 R9 RR.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof CM as (Hc0 & Hc64 & _).
  destruct (blk_range C A M md (Z_to_bv 64 pixd) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A M md (Z_to_bv 64 cd) 24 CK HW Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  destruct (ss_dims al_rom r M s pixd (hdv w h d cd data) ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ALp PX ltac:(lia) (W_sok_win C A M md (s - 144) 144 CK HW ltac:(lia) ltac:(cbn; lia)) R2 R19)
    as (r1 & RUN1 & Q2 & Q19 & AG1). cbn [p_w p_h hdv] in RUN1.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C Ar s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (OUT1 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> M1 x = M x).
  { intros x Hx. subst M1. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (CE1 : cellsZ M1 (frame13 s ret (svr13 regs))) by (eapply (cells13_out M M1 (s - 112) (s - 104)); [exact OUT1 | lia | lia | lia | exact CE]).
  assert (PX1 : PIXat M1 pixd (hdv w h d cd data)) by (apply (PIXat_frame M); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (CM1 : CMAPat M1 cd (cset_n cv n')) by (apply (CMAPat_frame M); [exact CM | intros x Hx; apply OUT1; lia]).
  assert (Cidx1 : rdn SEGS M1 (Z_to_bv 64 (s - 132)) 4 = Some ibs).
  { rewrite <- Cidx. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUT1. lia. }
  assert (Cw1 : rdn SEGS M1 (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w)) by (subst M1; rd4 w).
  assert (Ch1 : rdn SEGS M1 (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h)) by (subst M1; rd4 h).
  assert (Y18 : getr r1 18 = Z_to_bv 64 bx) by (rewrite (AG1 18) by notin_list; exact R18).
  assert (Y8 : getr r1 8 = Z_to_bv 64 2) by (rewrite (AG1 8) by notin_list; exact R8).
  assert (Y9 : getr r1 9 = Z_to_bv 64 d) by (rewrite (AG1 9) by notin_list; exact R9).
  assert (RR1 : forall x, In x sc_rest -> getr r1 x = getr regs x) by (unfold sc_rest in *; rest_solve).
  destruct HBX as [BX0 | (BX & Lb & NEbd)].
  - (* [comment removed for export] *)
    subst bx.
    destruct (ss_F0 al_rom r1 M1 s pixd w h (hdv w h d cd data) ltac:(lia) ltac:(lia) ltac:(lia) ALp PX1 ltac:(lia) ltac:(lia) ltac:(lia) Cw1 Ch1
                (W_sok_win C A M1 md (s - 144) 144 CK HW1 ltac:(lia) ltac:(cbn; lia)) Q2 Y18 Q19)
      as (r2 & RUN2 & V2 & V10 & V18 & V20 & V21 & V19 & AG2). cbn [p_wpl p_data hdv] in V10, V18.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    set (M2 := wbytes (wbytes M1 _ _) _ _).
    assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2) by (subst M2; wp_win CK).
    destruct WP2 as [HW2 PM2].
    assert (OUT2 : forall x : word, ~ (s - 120 <= u x < s - 112)%Z -> M2 x = M1 x).
    { intros x Hx. subst M2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    apply (sel_loop_W C Ar A m md regs s pixd 0 w h d cd data 0 w 0 h n' cv ibs ret S M2 r2 CK HK SUB Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW2 PM2).
    + eapply (cells13_out M1 M2 (s - 120) (s - 112)); [exact OUT2 | lia | lia | lia | exact CE1].
    + apply (PIXat_frame M1); [exact PX1 | intros x Hx; apply OUT2; lia].
    + exact HOK. + exact Hw. + exact Hh. + exact Hd. + exact Lp. + exact Ld. + exact LdA. + exact Ld0. + exact Hcd.
    + apply (CMAPat_frame M1); [exact CM1 | intros x Hx; apply OUT2; lia].
    + exact Hn'. + exact Lc. + exact NEpd. + exact NEcd.
    + intros NZ. exfalso. exact (NZ eq_refl).
    + lia. + lia. + lia. + lia.
    + rewrite <- Cw1. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUT2. lia.
    + subst M2. rd4 h.
    + subst M2. rd4 0%Z.
    + subst M2. rd4 0%Z.
    + rewrite <- Cidx1. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUT2. lia.
    + exact V2. + exact V10. + rewrite (AG2 8) by notin_list; exact Y8. + rewrite (AG2 9) by notin_list; exact Y9. + exact V18. + exact V20. + exact V21.
    + unfold sc_rest in *. rest_solve.
  - (* [comment removed for export] *)
    pose proof BX as (Hb1 & Hb64 & _).
    destruct (blk_range C A M md (Z_to_bv 64 bx) 20 CK HW Lb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
    assert (BX1 : BOXat M1 bx 278 35 122 50 1) by (apply (BOXat_frame M); [exact BX | intros x Hx; apply OUT1; lia]).
    destruct (ss_F al_rom r1 M1 s bx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Q2 Y18) as (r2 & RUN2 & V1 & V10 & V11 & V12 & V13 & V14 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    pose proof (ai_live_hull A M (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lb) as (_ & ALb & _). rewrite u_Z2bv in ALb by lia.
    destruct (bg_seg al_rom r2 M1 bx 278 35 122 50 (s - 116) (s - 120) (s - 124) (s - 128) (Z_to_bv 64 0x16aac)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) BX1 Gb ALb ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                (W_sok_win C A M1 md (s - 128) 16 CK HW1 ltac:(lia) ltac:(cbn; lia)) ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12 V13 V14)
      as (r3 & RUN3 & X1 & X10 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    replace (Z_to_bv 64 0x16aac) with (0x16aac : word) by (apply bv_eq; reflexivity).
    set (M2 := wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M1 _ _) _ _) _ _) _ _) _ _) _ _) _ _) _ _).
    assert (WP2 : W C A M2 md /\ POSTM C Ar s m M2) by (subst M2; wp_win CK).
    destruct WP2 as [HW2 PM2].
    assert (OUT2 : forall x : word, ~ (s - 128 <= u x < s - 112)%Z -> M2 x = M1 x).
    { intros x Hx. subst M2. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (PX2 : PIXat M2 pixd (hdv w h d cd data)) by (apply (PIXat_frame M1); [exact PX1 | intros x Hx; apply OUT2; lia]).
    assert (X2 : getr r3 2 = Z_to_bv 64 (s - 144)) by (rewrite (AG3 2), (AG2 2) by notin_list; exact Q2).
    assert (X19 : getr r3 19 = Z_to_bv 64 pixd) by (rewrite (AG3 19), (AG2 19) by notin_list; exact Q19).
    destruct (ss_G al_rom r3 M2 s pixd 278 35 122 50 (hdv w h d cd data) ltac:(lia) ltac:(lia) ltac:(lia) ALp PX2
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(subst M2; rd4 278%Z) ltac:(subst M2; rd4 35%Z) ltac:(subst M2; rd4 122%Z) ltac:(subst M2; rd4 50%Z) X2 X19)
      as (r4 & RUN4 & Z2 & Z10 & Z18 & Z20 & Z21 & Z19 & AG4). cbn [p_wpl p_data hdv] in Z10, Z18.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    apply (sel_loop_W C Ar A m md regs s pixd bx w h d cd data 278 (278 + 122 - 1) 35 (35 + 50 - 1) n' cv ibs ret S M2 r4 CK HK SUB Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW2 PM2).
    + eapply (cells13_out M1 M2 (s - 128) (s - 112)); [exact OUT2 | lia | lia | lia | exact CE1].
    + exact PX2.
    + exact HOK. + exact Hw. + exact Hh. + exact Hd. + exact Lp. + exact Ld. + exact LdA. + exact Ld0. + exact Hcd.
    + apply (CMAPat_frame M1); [exact CM1 | intros x Hx; apply OUT2; lia].
    + exact Hn'. + exact Lc. + exact NEpd. + exact NEcd.
    + intros _. split; [| split; [exact Lb | exact NEbd]]. apply (BOXat_frame M1); [exact BX1 | intros x Hx; apply OUT2; lia].
    + lia. + lia. + lia. + lia.
    + rewrite <- Cw1. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUT2. lia.
    + rewrite <- Ch1. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUT2. lia.
    + subst M2. rd4 278%Z.
    + subst M2. rd4 35%Z.
    + rewrite <- Cidx1. apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUT2. lia.
    + exact Z2. + exact Z10. + rewrite (AG4 8), (AG3 8), (AG2 8) by notin_list; exact Y8. + rewrite (AG4 9), (AG3 9), (AG2 9) by notin_list; exact Y9.
    + exact Z18. + exact Z20. + exact Z21.
    + unfold sc_rest in *. rest_solve.
Qed.

(* [comment removed for export] *)
Theorem pixSetSelectCmap_W : forall C Ar A m md regs (s pixd bx w h d cd data : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 bx -> getr regs 12 = Z_to_bv 64 2 ->
  getr regs 13 = Z_to_bv 64 255 -> getr regs 14 = Z_to_bv 64 255 -> getr regs 15 = Z_to_bv 64 100 ->
  PIXat m pixd (hdv w h d cd data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z ->
  live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None -> Z_to_bv 64 pixd <> Z_to_bv 64 data ->
  (cd = 0%Z \/ (CMAPat m cd cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cd) = Some 24%Z /\ live Ar (Z_to_bv 64 cd) = None /\ live (c_A0 C) (Z_to_bv 64 cd) = None /\
                 live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\ live Ar (Z_to_bv 64 (c_arr cv)) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                 Z_to_bv 64 cd <> Z_to_bv 64 data /\ Z_to_bv 64 cd <> Z_to_bv 64 (c_arr cv) /\ Z_to_bv 64 pixd <> Z_to_bv 64 cd /\ Z_to_bv 64 pixd <> Z_to_bv 64 (c_arr cv))) ->
  (bx = 0%Z \/ (BOXat m bx 278 35 122 50 1 /\ live A (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data /\
                 (cd <> 0%Z -> Z_to_bv 64 bx <> Z_to_bv 64 cd /\ Z_to_bv 64 bx <> Z_to_bv 64 (c_arr cv)))) ->
  SK C Ar A m md regs s pixd bx w h d cd data cv ret S ->
  realizes SEGS (mkCfg (mkst regs (0x168ac : word) m al_rom) md) S.
Proof.
  intros C Ar A m md regs s pixd bx w h d cd data cv ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 PX HOK Hw Hh Lp Ld LdA Ld0 NEpd HCM HBX HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz). pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl. pose proof (dval_range d DV) as Hd32.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md (Z_to_bv 64 pixd) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  assert (Hbx : (0 <= bx < 2 ^ 64)%Z) by (destruct HBX as [-> | ((Hb1 & Hb64 & _) & _)]; lia).
  (* [comment removed for export] *)
  destruct (ss_P al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 144) 144 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1) as (r0 & RUN0 & P2 & P1 & AG0).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN0 |].
  assert (WP0 : W C A (FR13 m s ret regs) md /\ POSTM C Ar s m (FR13 m s ret regs)).
  { unfold FR13. wp_win CK. }
  destruct WP0 as [HW0 PM0]. set (M0 := FR13 m s ret regs) in *.
  pose proof (cells_FR13 m s ret regs ltac:(lia) ltac:(lia)) as CE0. fold M0 in CE0.
  assert (OUT0 : forall x : word, ~ (s - 144 <= u x < s)%Z -> M0 x = m x).
  { intros x Hx. subst M0. unfold FR13. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PX0 : PIXat M0 pixd (hdv w h d cd data)) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT0; lia]).
  assert (RR0 : forall x, In x sc_rest -> getr r0 x = getr regs x) by (unfold sc_rest; rest_solve).
  assert (HBX0 : bx <> 0%Z -> (1 <= bx)%Z /\ (bx + 20 <= alloc_top (c_vm C))%Z /\ BOXat M0 bx 278 35 122 50 1).
  { intros NZ. destruct HBX as [-> | (BX & Lb & _ & _)]; [exfalso; exact (NZ eq_refl)|]. pose proof BX as (Hb1 & Hb64 & _).
    destruct (blk_range C A m md (Z_to_bv 64 bx) 20 CK HW Lb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
    split; [lia|]. split; [lia|]. apply (BOXat_frame m); [exact BX | intros x Hx; apply OUT0; lia]. }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  (* [comment removed for export] *)
  destruct (ss_A al_rom r0 M0 pixd bx (hdv w h d cd data) ltac:(lia) ALp PX0 Hbx ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
              ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r1 & RUN1 & Q10 & Q20 & Q21 & Q22 & Q8 & Q18 & Q19 & Q2 & AG1). cbn [p_cmap hdv] in Q10. rewrite P2 in Q2.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
  assert (RR1 : forall x, In x sc_rest -> getr r1 x = getr regs x) by (unfold sc_rest in *; rest_solve).
  destruct HCM as [CD0 | (CM & CMOK & Lc & LcA & Lc0 & La & LaA & La0 & NEcd & NEca & NEpc & NEpa)].
  - (* [comment removed for export] *)
    rewrite CD0 in Q10.
    destruct (ss_B0 al_rom r1 M0 Q10) as (r2 & RUN2 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
    apply (sel_err_W C Ar A m md regs s pixd bx w h d cd data cv ret S M0 r2 0x169c4 0x108f0 CK HK SUB Hs16 ltac:(unfold LSF; lia) Hhi Hret
             ltac:(cbn; right; left; reflexivity) HW0 PM0 CE0 ltac:(lia) TOPp PX0).
    + intros NZ. exfalso. exact (NZ CD0).
    + exact HBX0.
    + rewrite (AG2 2) by notin_list. exact Q2.
    + intros x Hx. rewrite (AG2 x) by notin_list. exact (RR1 x Hx).
    + exact H2.
  - pose proof CM as (Hc0 & Hc64 & CWF & _). pose proof CMOK as (Hcdp & Hcna & Hcn & Hcarr). pose proof (cf_arr _ CWF) as Rarr.
    assert (Hpow : (2 <= c_nalloc cv <= 256)%Z) by (rewrite Hcna; destruct Hcdp as [->|[->|[->| ->]]]; cbn; lia). clear Hcdp.
    destruct (blk_range C A m md (Z_to_bv 64 cd) 24 CK HW Lc ltac:(lia)) as [Gc TOPc]. rewrite u_Z2bv in Gc, TOPc by lia.
    destruct (blk_range C A m md (Z_to_bv 64 (c_arr cv)) _ CK HW La ltac:(lia)) as [Ga TOPa]. rewrite u_Z2bv in Ga, TOPa by lia.
    pose proof (blk_apart C A m md _ _ _ _ CK HW Lc La NEca ltac:(lia) ltac:(lia)) as APca. rewrite !u_Z2bv in APca by lia. apply box_i in APca.
    pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lc) as (_ & ALc & _). rewrite u_Z2bv in ALc by lia.
    assert (ALc8 : (cd mod 8 = 0)%Z) by (apply al16_mod8; exact ALc).
    assert (CM0 : CMAPat M0 cd cv) by (apply (CMAPat_frame m); [exact CM | intros x Hx; apply OUT0; lia]).
    assert (HCM0 : cd <> 0%Z -> (1 <= cd)%Z /\ (cd + 24 <= alloc_top (c_vm C))%Z /\ exists n', (1 <= n' <= c_nalloc cv)%Z /\ CMAPat M0 cd (cset_n cv n')).
    { intros _. split; [lia|]. split; [lia|]. exists (c_n cv). split; [lia|]. apply cset_n_self. exact CM0. }
    destruct (Z_lt_ge_dec 8 d) as [D8|D8].
    { (* [comment removed for export] *)
      destruct (ss_Bd al_rom r1 M0 pixd cd (hdv w h d cd data) ltac:(lia) ALp PX0 ltac:(lia) ltac:(lia) ltac:(cbn; lia) Q10 Q19) as (r2 & RUN2 & AG2).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
      apply (sel_err_W C Ar A m md regs s pixd bx w h d cd data cv ret S M0 r2 0x16a14 0x10891 CK HK SUB Hs16 ltac:(unfold LSF; lia) Hhi Hret
               ltac:(cbn; do 3 right; left; reflexivity) HW0 PM0 CE0 ltac:(lia) TOPp PX0 HCM0 HBX0).
      + rewrite (AG2 2) by notin_list. exact Q2.
      + intros x Hx. rewrite (AG2 x) by (unfold sc_rest in Hx; cbn in Hx; destruct Hx as [<-|[<-|[]]]; notin_list). exact (RR1 x Hx).
      + exact H2. }
    assert (Hd : (d = 1 \/ d = 2 \/ d = 4 \/ d = 8)%Z) by (unfold dval in DV; lia).
    destruct (Z_lt_ge_dec 2 (c_n cv)) as [N2|N2].
    2:{ (* [comment removed for export] *)
      destruct (ss_Bn al_rom r1 M0 pixd cd (hdv w h d cd data) cv ltac:(lia) ALp PX0 ltac:(lia) ALc CM0 Hd ltac:(lia) Q10 Q19 Q8) as (r2 & RUN2 & AG2).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
      apply (sel_err_W C Ar A m md regs s pixd bx w h d cd data cv ret S M0 r2 0x169ec 0x10368 CK HK SUB Hs16 ltac:(unfold LSF; lia) Hhi Hret
               ltac:(cbn; do 2 right; left; reflexivity) HW0 PM0 CE0 ltac:(lia) TOPp PX0 HCM0 HBX0).
      + rewrite (AG2 2) by notin_list. exact Q2.
      + intros x Hx. rewrite (AG2 x) by (unfold sc_rest in Hx; cbn in Hx; destruct Hx as [<-|[<-|[]]]; notin_list). exact (RR1 x Hx).
      + exact H2. }
    (* [comment removed for export] *)
    destruct (ss_B al_rom r1 M0 s pixd cd (hdv w h d cd data) cv ltac:(lia) ALp PX0 ltac:(lia) ALc CM0 Hd N2 Q2 Q10 Q19 Q8 Q20 Q21 Q22)
      as (r2 & RUN2 & V2 & V1 & V10 & V11 & V12 & V13 & V14 & V9 & V23 & V24 & AG2). cbn [p_d hdv] in V9.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
    assert (DEF0 : forall a : word, (c_arr cv <= u a < c_arr cv + 4 * c_n cv)%Z -> M0 a <> None).
    { intros a Ha. destruct (blk_byte C A M0 md (Z_to_bv 64 (c_arr cv)) _ a CK HW0 La ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact D. }
    destruct (gi_W al_rom r2 M0 cd (s - 132) cv (Z_to_bv 64 0x16958) ltac:(lia) ALc8 CM0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply sp_slot_al4'; [exact Hs16 | reflexivity]) ltac:(lia) ltac:(lia) DEF0
                (W_sok_win C A M0 md (s - 132) 4 CK HW0 ltac:(lia) ltac:(cbn; lia)) V1 ltac:(red; apply bv_eq; reflexivity) V10 V14 V11 V12 V13)
      as (r3 & m3 & RUN3 & RES & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN3 |].
    replace (Z_to_bv 64 0x16958) with (0x16958 : word) by (apply bv_eq; reflexivity).
    assert (RR3 : forall x, In x sc_rest -> getr r3 x = getr regs x).
    { intros x Hx. rewrite (AG3 x), (AG2 x) by (unfold sc_rest in Hx; cbn in Hx; destruct Hx as [<-|[<-|[]]]; notin_list). exact (RR1 x Hx). }
    assert (Y2 : getr r3 2 = Z_to_bv 64 (s - 144)) by (rewrite (AG3 2) by notin_list; exact V2).
    assert (Y19 : getr r3 19 = Z_to_bv 64 pixd) by (rewrite (AG3 19), (AG2 19) by notin_list; exact Q19).
    assert (Y18 : getr r3 18 = Z_to_bv 64 bx) by (rewrite (AG3 18), (AG2 18) by notin_list; exact Q18).
    assert (Y8 : getr r3 8 = Z_to_bv 64 2) by (rewrite (AG3 8), (AG2 8) by notin_list; exact Q8).
    assert (Y9 : getr r3 9 = Z_to_bv 64 d) by (rewrite (AG3 9) by notin_list; exact V9).
    assert (Y23 : getr r3 23 = Z_to_bv 64 cd) by (rewrite (AG3 23) by notin_list; exact V23).
    assert (Y24 : getr r3 24 = Z_to_bv 64 (c_n cv)) by (rewrite (AG3 24) by notin_list; exact V24).
    assert (Y20 : getr r3 20 = Z_to_bv 64 100) by (rewrite (AG3 20), (AG2 20) by notin_list; exact Q20).
    assert (Y21 : getr r3 21 = Z_to_bv 64 255) by (rewrite (AG3 21), (AG2 21) by notin_list; exact Q21).
    assert (Y22 : getr r3 22 = Z_to_bv 64 255) by (rewrite (AG3 22), (AG2 22) by notin_list; exact Q22).
    (* [comment removed for export] *)
    assert (GI : exists ibs, (forall x : word, ~ (s - 132 <= u x < s - 128)%Z -> m3 x = M0 x) /\ rdn SEGS m3 (Z_to_bv 64 (s - 132)) 4 = Some ibs /\ mem_grows M0 m3).
    { destruct RES as [[_ ->] | (_ & i' & _ & ->)].
      - exists (word_to_le_bytes 4 (Z_to_bv 64 0)). split; [| split; [apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia | apply wbytes_grows]].
        intros x Hx. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.
      - exists (word_to_le_bytes 4 (Z_to_bv 64 i')). split; [| split; [apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia | eapply mem_grows_trans; apply wbytes_grows]].
        intros x Hx. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    destruct GI as (ibs & OUT3 & Cidx3 & GR3).
    assert (HW3 : W C A m3 md).
    { apply (W_local C A M0 md m3 s CK HW0 Hhi); [| exact GR3]. intros a NE. left. unfold scratch.
      destruct (Z_lt_ge_dec (u a) (s - 132)); [exfalso; apply NE; apply OUT3; lia|]. destruct (Z_lt_ge_dec (u a) (s - 128)); [lia|]. exfalso; apply NE; apply OUT3; lia. }
    assert (PM3 : POSTM C Ar s m m3).
    { eapply POSTM_trans; [exact PM0|]. apply (POSTM_sub C Ar A _ _ _ SUB). eapply (POSTM_range C A M0 md m3); [exact CK | exact HW0 | exact OUT3 | lia | lia | lia]. }
    assert (CE3 : cellsZ m3 (frame13 s ret (svr13 regs))) by (eapply (cells13_out M0 m3 (s - 132) (s - 128)); [exact OUT3 | lia | lia | lia | exact CE0]).
    assert (PX3 : PIXat m3 pixd (hdv w h d cd data)) by (apply (PIXat_frame M0); [exact PX0 | intros x Hx; apply OUT3; lia]).
    assert (CM3 : CMAPat m3 cd cv) by (apply (CMAPat_frame M0); [exact CM0 | intros x Hx; apply OUT3; lia]).
    assert (HBX3 : bx = 0%Z \/ (BOXat m3 bx 278 35 122 50 1 /\ live A (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data /\
                   Z_to_bv 64 bx <> Z_to_bv 64 cd /\ Z_to_bv 64 bx <> Z_to_bv 64 (c_arr cv))).
    { destruct HBX as [Z0 | (BX & Lb & NEbd & NEb2)]; [left; exact Z0 | right]. split; [| split; [exact Lb | split; [exact NEbd | apply NEb2; lia]]].
      destruct (HBX0 ltac:(intros ->; pose proof BX as (Hb1 & _); lia)) as (Hb1 & TOPb & BX0). apply (BOXat_frame M0); [exact BX0 | intros x Hx; apply OUT3; lia]. }
    destruct RES as [[A1 _] | (A0 & _)].
    + (* [comment removed for export] *)
      destruct (ss_C1 al_rom r3 m3 cd A1 Y23 Y20 Y21 Y22) as (r4 & RUN4 & X1 & X10 & X11 & X12 & X13 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
      destruct (Z_lt_ge_dec (c_n cv) (c_nalloc cv)) as [ROOM|FULL].
      * (* [comment removed for export] *)
        pose proof (blk_sok C A m3 md (c_arr cv) (4 * c_nalloc cv) CK HW3 La ltac:(lia) ltac:(lia) ltac:(lia)) as SOKa.
        destruct (ac_ok al_rom r4 m3 cd cv (Z_to_bv 64 0x16970) ltac:(lia) ALc8 CM3 ROOM ltac:(lia) ltac:(lia) (box_e _ APca)
                    ltac:(eapply store_ok_sub; [| exact SOKa | |]; rewrite ?u_Z2bv by lia; lia)
                    (blk_sok C A m3 md cd 24 CK HW3 Lc ltac:(lia) ltac:(lia) ltac:(lia)) X1 ltac:(red; apply bv_eq; reflexivity) X10 X11 X12 X13)
          as (r5 & RUN5 & Z10 & AG5).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
        replace (Z_to_bv 64 0x16970) with (0x16970 : word) by (apply bv_eq; reflexivity).
        set (Ma := wbytes (wbytes (wbytes (wbytes m3 _ _) _ _) _ _) _ _).
        set (M5 := wbytes Ma (Z_to_bv 64 (cd + 16)) (word_to_le_bytes 4 (Z_to_bv 64 (c_n cv + 1)))).
        assert (WPa : W C A Ma md /\ POSTM C Ar s m Ma).
        { subst Ma. do 4 (apply (WP_blk C Ar A m _ _ (Z_to_bv 64 (c_arr cv)) _ (4 * c_nalloc cv)); [exact CK | | exact La | exact LaA | exact La0 | exact SUB | rewrite !u_Z2bv by lia; lia | cbn [length]; rewrite !u_Z2bv by lia; lia]).
          split; [exact HW3 | exact PM3]. }
        assert (WP5 : W C A M5 md /\ POSTM C Ar s m M5).
        { subst M5. apply (WP_blk C Ar A m _ _ (Z_to_bv 64 cd) _ 24); [exact CK | exact WPa | exact Lc | exact LcA | exact Lc0 | exact SUB | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]. }
        destruct WP5 as [HW5 PM5].
        assert (OUTa : forall x : word, ~ (c_arr cv + 4 * c_n cv <= u x < c_arr cv + 4 * c_n cv + 4)%Z -> Ma x = m3 x).
        { intros x Hx. subst Ma. rewrite !wbytes_outside; cbn [length]; rewrite ?u_Z2bv by lia; try lia. reflexivity. }
        assert (OUT5 : forall x : word, ~ (cd + 16 <= u x < cd + 20)%Z -> M5 x = Ma x).
        { intros x Hx. subst M5. apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia. }
        assert (CM5 : CMAPat M5 cd (cset_n cv (c_n cv + 1))).
        { subst M5. apply CMAP_wr_n; [| pose proof (cf_n _ CWF); lia]. pose proof (box_e _ APca) as U. apply (CMAPat_frame m3); [exact CM3 | intros x Hx; apply OUTa; lia]. }
        pose proof (blk_apart C A m md _ _ _ _ CK HW Lp La NEpa ltac:(lia) ltac:(lia)) as APpa. rewrite !u_Z2bv in APpa by lia.
        pose proof (blk_apart C A m md _ _ _ _ CK HW Lp Lc NEpc ltac:(lia) ltac:(lia)) as APpc. rewrite !u_Z2bv in APpc by lia.
        assert (PX5 : PIXat M5 pixd (hdv w h d cd data)) by (apply (PIXat_frame m3); [exact PX3 | intros x Hx; rewrite OUT5 by lia; apply OUTa; lia]).
        clear APpa APpc.
        assert (CE5 : cellsZ M5 (frame13 s ret (svr13 regs))).
        { eapply (cells13_out Ma M5 (cd + 16) (cd + 20)); [exact OUT5 | lia | lia | lia |]. eapply (cells13_out m3 Ma (c_arr cv + 4 * c_n cv) (c_arr cv + 4 * c_n cv + 4)); [exact OUTa | lia | lia | lia | exact CE3]. }
        assert (Cidx5 : rdn SEGS M5 (Z_to_bv 64 (s - 132)) 4 = Some ibs).
        { rewrite <- Cidx3. etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; rewrite u_Z2bv in Hx by lia; cbn in Hx; rewrite OUT5 by lia; apply OUTa; lia] | reflexivity]. }
        assert (HBX5 : bx = 0%Z \/ (BOXat M5 bx 278 35 122 50 1 /\ live A (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data)).
        { destruct HBX3 as [Z0 | (BX & Lb & NEbd & NEbc & NEba)]; [left; exact Z0 | right]. split; [| split; [exact Lb | exact NEbd]]. pose proof BX as (Hb1 & Hb64 & _).
          pose proof (blk_apart C A m md _ _ _ _ CK HW Lb La NEba ltac:(lia) ltac:(lia)) as APba. rewrite !u_Z2bv in APba by lia.
          pose proof (blk_apart C A m md _ _ _ _ CK HW Lb Lc NEbc ltac:(lia) ltac:(lia)) as APbc. rewrite !u_Z2bv in APbc by lia.
          apply (BOXat_frame m3); [exact BX | intros x Hx; rewrite OUT5 by lia; apply OUTa; lia]. }
        assert (Z2 : getr r5 2 = Z_to_bv 64 (s - 144)) by (rewrite (AG5 2), (AG4 2) by notin_list; exact Y2).
        assert (Z24 : getr r5 24 = Z_to_bv 64 (c_n cv)) by (rewrite (AG5 24), (AG4 24) by notin_list; exact Y24).
        destruct (ss_D0 al_rom r5 M5 s (c_n cv) ltac:(lia) ltac:(lia) ltac:(lia) (W_sok_win C A M5 md (s - 144) 144 CK HW5 ltac:(lia) ltac:(cbn; lia)) Z2 Z10 Z24)
          as (r6 & RUN6 & AG6).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
        set (M6 := wbytes M5 _ _).
        assert (WP6 : W C A M6 md /\ POSTM C Ar s m M6) by (subst M6; wp_win CK).
        destruct WP6 as [HW6 PM6].
        assert (OUT6 : forall x : word, ~ (s - 132 <= u x < s - 128)%Z -> M6 x = M5 x) by (intros x Hx; subst M6; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia).
        apply (sel_tail_W C Ar A m md regs s pixd bx w h d cd data (c_n cv + 1) cv (word_to_le_bytes 4 (Z_to_bv 64 (c_n cv))) ret S M6 r6 CK HK SUB Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW6 PM6).
        -- eapply (cells13_out M5 M6 (s - 132) (s - 128)); [exact OUT6 | lia | lia | lia | exact CE5].
        -- apply (PIXat_frame M5); [exact PX5 | intros x Hx; apply OUT6; lia].
        -- exact HOK. -- exact Hw. -- exact Hh. -- exact Hd. -- exact Lp. -- exact Ld. -- exact LdA. -- exact Ld0. -- lia.
        -- apply (CMAPat_frame M5); [exact CM5 | intros x Hx; apply OUT6; lia].
        -- lia. -- exact Lc. -- exact NEpd. -- exact NEcd.
        -- destruct HBX5 as [Z0 | (BX & Lb & NEbd)]; [left; exact Z0 | right]. split; [| split; [exact Lb | exact NEbd]]. pose proof BX as (Hb1 & Hb64 & _).
           apply (BOXat_frame M5); [exact BX | intros x Hx; apply OUT6; lia].
        -- subst M6. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia.
        -- rewrite (AG6 2) by notin_list. exact Z2.
        -- rewrite (AG6 19), (AG5 19), (AG4 19) by notin_list. exact Y19.
        -- rewrite (AG6 18), (AG5 18), (AG4 18) by notin_list. exact Y18.
        -- rewrite (AG6 8), (AG5 8), (AG4 8) by notin_list. exact Y8.
        -- rewrite (AG6 9), (AG5 9), (AG4 9) by notin_list. exact Y9.
        -- intros x Hx. rewrite (AG6 x), (AG5 x), (AG4 x) by (unfold sc_rest in Hx; cbn in Hx; destruct Hx as [<-|[<-|[]]]; notin_list). exact (RR3 x Hx).
      * (* [comment removed for export] *)
        destruct (ac_full al_rom r4 m3 cd cv ltac:(lia) ALc8 CM3 ltac:(lia) (W_sev_got C A m3 md HW3) (W_sev C A m3 md HW3) X10) as (r5 & RUN5 & Z10 & Z11 & Z12 & Z1 & Z2 & AG5).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN5 |].
        rewrite X1 in Z1. rewrite (AG4 2) in Z2 by notin_list. rewrite Y2 in Z2.
        apply (returnErrorInt_W C A m3 md r5 (s - 144) 0x10b69 0x10abb 21 15 (Z_to_bv 64 0x16970) (Z_to_bv 64 1) S CK HW3 Z2
                 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Z1 ltac:(red; apply bv_eq; reflexivity) Z10 Z11 Z12 str_no_free str_pixcmapAddColor).
        intros m4 r6 HW4 OUT4 GR4 CS4 B10. unfold LSF in OUT4.
        replace (Z_to_bv 64 0x16970) with (0x16970 : word) by (apply bv_eq; reflexivity).
        assert (W2 : getr r6 2 = Z_to_bv 64 (s - 144)) by (csr; reflexivity).
        destruct (ss_D1 al_rom r6 m4 s (W_sev_got C A m4 md HW4) (W_sev C A m4 md HW4) W2 B10) as (r7 & RUN7 & U2 & U1 & U10 & U11 & U12 & AG7).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN7 |].
        apply (returnErrorInt_W C A m4 md r7 (s - 144) 0x10c63 0x10d41 23 16 (Z_to_bv 64 0x16d5c) (Z_to_bv 64 1) S CK HW4 U2
                 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) U1 ltac:(red; apply bv_eq; reflexivity) U10 U11 U12 str_adding str_pixSetSelectCmap).
        intros m5 r8 HW5 OUT5 GR5 CS5 C10. unfold LSF in OUT5.
        replace (Z_to_bv 64 0x16d5c) with (0x16d5c : word) by (apply bv_eq; reflexivity).
        destruct (ss_J al_rom r8 m5) as (r9 & RUN9 & AG9).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN9 |].
        assert (CE5 : cellsZ m5 (frame13 s ret (svr13 regs))).
        { eapply (cells13_out m4 m5 _ _); [exact OUT5 | lia | lia | lia |]. eapply (cells13_out m3 m4 _ _); [exact OUT4 | lia | lia | lia | exact CE3]. }
        destruct (ss_RET al_rom r9 m5 s ret (svr13 regs) (Z_to_bv 64 1) ltac:(lia) ltac:(lia) Hret CE5 ltac:(rewrite (AG9 2) by notin_list; csr; reflexivity) ltac:(rewrite (AG9 10) by notin_list; exact C10))
          as (r10 & RUN10 & E2 & E1 & E10 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & AG10).
        eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN10 |].
        unfold svr13 in *.
        apply (HK m5 r10 HW5).
        -- apply cs_kept_intro; csr; try reflexivity. all: rewrite ?E8, ?E9, ?E18, ?E19, ?E20, ?E21, ?E22, ?E23, ?E24, ?E25, ?E26, ?E27; try reflexivity.
           all: rewrite (AG9 _) by notin_list; csr; rewrite (AG5 _), (AG4 _) by notin_list; unfold sc_rest in RR3; rewrite RR3 by (cbn; tauto); reflexivity.
        -- eapply POSTM_trans; [exact PM3|]. apply (POSTM_sub C Ar A _ _ _ SUB).
           eapply POSTM_trans; [eapply (POSTM_range C A m3 md m4); [exact CK | exact HW3 | exact OUT4 | lia | lia | lia] |].
           eapply (POSTM_range C A m4 md m5); [exact CK | exact HW4 | exact OUT5 | lia | lia | lia].
        -- apply (PIXat_frame m3); [exact PX3 | intros x Hx; rewrite OUT5 by lia; apply OUT4; lia].
        -- intros _. exists (c_n cv). split; [lia|]. apply cset_n_self. apply (CMAPat_frame m3); [exact CM3 | intros x Hx; rewrite OUT5 by lia; apply OUT4; lia].
        -- intros NZ. destruct HBX3 as [Z0 | (BX & Lb & _ & _ & _)]; [exfalso; exact (NZ Z0)|]. pose proof BX as (Hb1 & Hb64 & _).
           destruct (blk_range C A m md (Z_to_bv 64 bx) 20 CK HW Lb ltac:(lia)) as [Gb TOPb]. rewrite u_Z2bv in Gb, TOPb by lia.
           apply (BOXat_frame m3); [exact BX | intros x Hx; rewrite OUT5 by lia; apply OUT4; lia].
    + (* [comment removed for export] *)
      destruct (ss_C0 al_rom r3 m3 A0) as (r4 & RUN4 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
      assert (HBX3' : bx = 0%Z \/ (BOXat m3 bx 278 35 122 50 1 /\ live A (Z_to_bv 64 bx) = Some 20%Z /\ Z_to_bv 64 bx <> Z_to_bv 64 data)).
      { destruct HBX3 as [Z0 | (BX & Lb & NEbd & _)]; [left; exact Z0 | right; split; [exact BX | split; [exact Lb | exact NEbd]]]. }
      apply (sel_tail_W C Ar A m md regs s pixd bx w h d cd data (c_n cv) cv ibs ret S m3 r4 CK HK SUB Hs16 ltac:(unfold LSF; lia) Hhi Hret H2 HW3 PM3 CE3 PX3 HOK Hw Hh Hd Lp Ld LdA Ld0
               ltac:(lia) (cset_n_self _ _ _ CM3) ltac:(lia) Lc NEpd NEcd HBX3' Cidx3).
      * rewrite (AG4 2) by notin_list. exact Y2.
      * rewrite (AG4 19) by notin_list. exact Y19.
      * rewrite (AG4 18) by notin_list. exact Y18.
      * rewrite (AG4 8) by notin_list. exact Y8.
      * rewrite (AG4 9) by notin_list. exact Y9.
      * intros x Hx. rewrite (AG4 x) by notin_list. exact (RR3 x Hx).
Qed.

(* [comment removed for export] *)
Theorem pixSetSelectCmap_null_W : forall C A m md regs (s bx : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 144 + 16 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x168ac : word) m al_rom) md) S.
Proof.
  intros C A m md regs s bx ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU21] in *. unfold LSF in *.
  destruct (ss_P al_rom regs m s ret ltac:(lia) ltac:(lia) (W_sok_win C A m md (s - 144) 144 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1) as (r0 & RUN0 & P2 & P1 & AG0).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN0 |].
  assert (WP0 : W C A (FR13 m s ret regs) md /\ POSTM C A s m (FR13 m s ret regs)) by (unfold FR13; wp_win CK).
  destruct WP0 as [HW0 PM0]. set (M0 := FR13 m s ret regs) in *.
  pose proof (cells_FR13 m s ret regs ltac:(lia) ltac:(lia)) as CE0. fold M0 in CE0.
  destruct (ss_A0 al_rom r0 M0 ltac:(rewrite (AG0 10) by notin_list; exact H10)) as (r1 & RUN1 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN1 |].
  destruct (ss_ehead al_rom 0x1699c 0x10298 r1 M0 s ltac:(cbn; left; reflexivity) (W_sev_got C A M0 md HW0) (W_sev C A M0 md HW0) ltac:(rewrite (AG1 2) by notin_list; exact P2))
    as (r2 & RUN2 & Q2 & Q10 & Q11 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN2 |].
  destruct (ss_etail al_rom r2 M0 s ret (svr13 regs) 0x10298 ltac:(lia) ltac:(lia) CE0 Q2 Q10 Q11)
    as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & V21 & V22 & V23 & V24 & V25 & V26 & V27 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact RUN3 |].
  unfold svr13 in *.
  apply (returnErrorInt_W C A M0 md r3 s 0x10298 0x10d41 16 16 ret (Z_to_bv 64 1) S CK HW0 V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret V10 V11 V12 str_pixs_not_defined str_pixSetSelectCmap).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity. all: rewrite ?V8, ?V9, ?V18, ?V19, ?V20, ?V21, ?V22, ?V23, ?V24, ?V25, ?V26, ?V27; try reflexivity.
    all: rewrite (AG2 _), (AG1 _), (AG0 _) by notin_list; reflexivity.
  - eapply POSTM_trans; [exact PM0|]. eapply (POSTM_range C A M0 md m4); [exact CK | exact HW0 | exact OUT4 | lia | lia | lia].
Qed.

End SelCmap.
