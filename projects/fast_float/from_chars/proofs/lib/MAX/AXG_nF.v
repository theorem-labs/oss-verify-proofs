(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatExec CatSim StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng AxBits MngZ MngRepr MngHeap MngImage MngSurgery MngCtx MngCtx2 MngExc MngNtfPre MngNtfC MngWb MngNtfM MngNtfS
                        AXF_eez AXG_ntfm AXG_ntfg AXG_nQ AXG_nM.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require AXF_dec63z.
Import ListNotations AX2 AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Ltac side := cbn [length word_to_le_bytes Z_to_le_bytes]; (rewrite ?u_wa_small by lia); lia.
Ltac peel := rewrite MngWb.wbytes_out by side.
Ltac memb := first [ AxSymRun3.memb_refl | repeat first [ (left; reflexivity) | right ] ].      (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma NC_add_zombie : forall L X EXC s m sp0 K g a, NC L X EXC s m sp0 K -> MT s g = Some (MUsed a) ->
  NC L (g :: X) (LMem (am_mem a) :: EXC) s m sp0 K.
Proof.
  intros L X EXC s m sp0 K g a N Hg. destruct N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD]. constructor; try assumption.
  - apply (repr_x_weaken L s _ EXC _ HR). intros l Hl. right. exact Hl.
  - intros l [<-|Hl]; [exists g, a; split; [left; reflexivity | split; [exact Hg | reflexivity]]|].
    destruct (HEX l Hl) as (x & b & Hx & Mx & El). exists x, b. split; [right; exact Hx | split; assumption].
  - intros x [<-|Hx]; [exists a; exact Hg | exact (HZU x Hx)].
Qed.

(* [comment removed for export] *)
Section FMM.
Variables (m : word -> option byte) (G sp0 H HP : Z).
Hypothesis Hsp : 2^20 <= sp0 <= 2^47.
Hypothesis HG : 1 <= G /\ G + 40 <= sp0 - 1024.

Definition fm_zero8 : list byte := word_to_le_bytes 8 (wa 0).

#[using="Type"] Lemma nth_zero8 : forall k, (k < 8)%nat -> nth k fm_zero8 (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros k Hk. do 8 (destruct k as [|k]; [reflexivity|]). lia. Qed.

#[using="Type"] Lemma le4_zero : forall k, (k < 4)%nat -> nth k (word_to_le_bytes 4 (wa 0)) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros k Hk. do 4 (destruct k as [|k]; [reflexivity|]). lia. Qed.
End FMM.

Section FM0M.
Variables (m : word -> option byte) (R : bvmap 5 word) (G sp0 BASE LEN canary ra s0 s1 s2 s3 : Z).
Hypothesis Hsp : 2^20 <= sp0 <= 2^47.
Hypothesis HG : 1 <= G /\ G + 40 <= sp0 - 1024.
Hypothesis HGo : G + 40 <= 0x10000 \/ 0x97000 <= G.
Let M' := OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0 m R G sp0 BASE LEN canary ra s0 s1 s2 s3.

#[using="Hsp HG"] Lemma fm0_out : forall x, 0 <= x < 2^64 -> ~ (sp0 - 88 <= x < sp0 - 48) -> ~ (G <= x < G + 40) -> ~ (614120 <= x < 614128) -> M' (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hsp HG : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2 H3. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. do 13 peel. reflexivity. Qed.
#[using="Hsp HG HGo"] Lemma fm0_G0 : forall k, (k < 8)%nat -> M' (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HGo : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HGo"] Lemma fm0_G8 : forall k, (k < 8)%nat -> M' (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HGo : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HGo"] Lemma fm0_G16 : forall k, (k < 8)%nat -> M' (wa (G + 16 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HGo : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. do 5 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HGo"] Lemma fm0_G24 : forall k, (k < 8)%nat -> M' (wa (G + 24 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HGo : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. do 4 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HGo"] Lemma fm0_G32 : forall k, (k < 8)%nat -> M' (wa (G + 32 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HGo : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. do 3 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma fm0_FMH : forall k, (k < 8)%nat -> M' (wa (614120 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins LiaFast.u0. intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. replace (614120 + Z.of_nat k) with (0 + 614120 + Z.of_nat k) by ring. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma fm0_grows : mem_grows m M'.
Proof. LiaFast.lf_pins LiaFast.u0. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0. repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. Qed.
End FM0M.

Section FM0.
Context {fx : FPState}.

#[using="Type"] Theorem seg_fm0 : forall L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len,
  NC L (g :: X) (LMem (am_mem a4) :: EXC) s4 m sp0 K -> EXC_z X s4 EXC -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa len -> getr R 12 = wa base -> getr R 18 = wa 0x95ed8 ->
  MT s4 g = Some (MUsed a4) -> ~ In g X -> st_free_meta_head s4 = None -> 0 <= base <= 2^64-1 -> 0 <= len <= 2^64-1 ->
  exists R' m', msteps SEGS (mkst R (wa 0x51bb4) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 base len /\
    free_meta g s4 = IRet (tt, s_fm0 s4 g) /\ NC L X EXC (s_fm0 s4 g) m' sp0 K /\ RS L (s_fm0 s4 g) s4 /\
    (forall x, In x X -> MT (s_fm0 s4 g) x = MT s4 x) /\ mem_grows m m' /\ FRM L s4 sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len N HEXo F R10 R11 R12 R18 Mg NXg Hfmh Rb Rl.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z _ s4 _ (proj1 HK) HEX) as HEO. pose proof HR as (_ & HPW & _).
  assert (Kg : In g (keys s4)) by (eapply MT_keys; exact Mg).
  set (G := loc_addr L (LMem g)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). fold G in G1, G2, G3, G4.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_pre R m G sp0 base len canary ra s0 s1 s2 s3).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3; lia); try (clear - Hsp1 HK1; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_fmh L s4 m _ HR HEO Hctx) as E; rewrite Hfmh in E; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s4 m _ HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; exact (rx_fmh_wr L s4 m _ HR HEO Hctx d n Hd Hn)) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_pfm0 R m rom G sp0 base len canary ra s0 s1 s2 s3 P ltac:(constructor)) as (R' & Hms & P1 & P2 & P8 & P9 & P10 & P11 & P12 & P13 & P18 & P19 & Poth).
  set (m' := OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm0z.fm0_mem_pfm0 m R G sp0 base len canary ra s0 s1 s2 s3) in *.
  set (SA := set_meta s4 g (MFree (Some g) (Some g))).
  assert (Es5 : s_fm0 s4 g = set_free_meta_head (Some g) SA) by reflexivity.
  set (s5 := s_fm0 s4 g) in *.
  assert (HKSA : KS SA) by (apply KS_set_meta; assumption).
  assert (HKs5 : KS s5) by (rewrite Es5; apply (KS_ctx SA); [reflexivity | reflexivity | exact HKSA]).
  assert (Ks5 : keys s5 = keys s4) by (rewrite Es5; change (keys (set_free_meta_head (Some g) SA)) with (keys SA); apply keys_set_meta; exact Kg).
  assert (MSAg : MT SA g = Some (MFree (Some g) (Some g))) by apply MT_set_same.
  assert (HRS : RS L s5 s4) by (rewrite Es5; apply (RS_trans L s4 SA); [apply RS_ctx_only; reflexivity | apply RS_set_free; assumption]).
  assert (HGr : 1 <= G /\ G + 40 <= sp0 - 1024) by (clear - G1 G2 HK1; lia).
  assert (HSP : 2^20 <= sp0 <= 2^47) by (clear - Hsp1 Hsp2 HK1; lia).
  set (Cn := meta_slot_cells g (Some (MFree (Some g) (Some g))) ++ [fmh_cell (Some g)]).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) Cn).
  { unfold Cn. cbn [meta_slot_cells app]. repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr fmh_cell] in *; rewrite ?loc_padd; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits, CTX_free_meta_head; fold G.
    all: try (change (loc_addr L (LCtx 16)) with (ly_ctx L + 16); rewrite Hctx).
    all: try (clear - HGr HSP; lia).
    all: intros n Hn; unfold m'.
    - apply fm0_G0; assumption.
    - apply fm0_G8; assumption.
    - apply fm0_G16; assumption.
    - rewrite fm0_G24 by (assumption || lia). f_equal. rewrite nth_zero8 by lia. rewrite le4_zero by lia. reflexivity.
    - replace (G + 28 + Z.of_nat n) with (G + 24 + Z.of_nat (n + 4)) by lia. rewrite fm0_G24 by (assumption || lia). f_equal.
      rewrite nth_zero8 by lia. rewrite le4_zero by lia. reflexivity.
    - apply fm0_G32; assumption.
    - replace (614104 + 16 + Z.of_nat n) with (614120 + Z.of_nat n) by ring. apply fm0_FMH; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply fm0_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (sp0 - 88 <= a < sp0 - 48) \/ (G <= a < G + 40) \/ (614120 <= a < 614128)).
  { intros a Ra Ha. destruct (decide (sp0 - 88 <= a < sp0 - 48)) as [A1|A1]; [left; exact A1|].
    destruct (decide (G <= a < G + 40)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (614120 <= a < 614128)) as [A3|A3]; [right; right; exact A3|].
    exfalso. apply Ha. unfold m'. apply fm0_out; assumption. }
  assert (Kg5 : In g (keys s5)) by (rewrite Ks5; exact Kg).
  assert (M5g : MT s5 g = Some (MFree (Some g) (Some g))) by (rewrite Es5; exact MSAg).
  assert (COV : forall c, In c (image s5) -> In c (REST s4 g) \/ In c Cn \/ In c (ctx_cells SA)).
  { intros c Hc. rewrite Es5 in Hc. destruct (cov_ctx_only SA (set_free_meta_head (Some g) SA) c eq_refl eq_refl Hc) as [H1|H1].
    - change (image SA) with (image (set_meta s4 g (MFree (Some g) (Some g)))) in H1.
      pose proof (image_set_key s4 g (MFree (Some g) (Some g)) HK Kg) as PP2.
      change (match MFree (Some g) (Some g) with MUsed am => group_cells g am | _ => [] end) with (@nil mcell) in PP2. rewrite app_nil_r in PP2.
      apply (Permutation_in c PP2) in H1. apply in_app_iff in H1 as [H1|H1]; [left; exact H1 | right; left; apply in_app_iff; left; exact H1].
    - destruct (cov_fmh SA (Some g) c H1) as [H2|H2]; [right; right; exact H2 | right; left; rewrite H2; apply in_app_iff; right; left; reflexivity]. }
  assert (CTXSA : forall c, In c (ctx_cells SA) -> In c (image s4)).
  { intros c Hc. apply ctx_in_image. exact Hc. }
  assert (REPR : repr_x L s5 (bview SEGS m') EXC).
  { apply (repr_x_drop L s5 _ (LMem (am_mem a4)) EXC).
    - apply (repr_x_next L s4 s5 (bview SEGS m) (bview SEGS m') _ Cn HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
      + intros c Hc. destruct (COV c Hc) as [H1|[H1|H1]]; [left; exact (In_REST_image s4 g c HK Kg H1) | right; exact H1 | left; exact (CTXSA c H1)].
      + intros c Hc. unfold Cn in Hc. apply in_app_iff in Hc as [Hc|[<-|[]]].
        * apply (Permutation_in c (Permutation_sym (image_decomp_key s5 g HKs5 Kg5))). rewrite M5g. apply in_app_iff. right. apply in_app_iff. left. exact Hc.
        * pose proof (fmh_cell_in s5) as E. rewrite Es5 in E |- *. exact E.
      + exact HNew.
      + intros a Ha. pose proof (bview_ne_range m m' a Ha) as Ra.
        assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
        destruct (CHG a Ra Ha') as [A|[A|A]].
        * right. intros c Hc _ Hin. destruct (RS_range L s5 s4 c HRS Hc) as (c0 & H0 & E0). pose proof (HC c0 H0) as (Q1 & Q2 & _).
          unfold in_rng, cell_range in Hin. unfold cell_range in E0. injection E0 as E1 E2. rewrite E1 in Q1. rewrite E1, E2 in Q2. cbn [fst snd] in Hin. clear - Hin Q1 Q2 A HK1. lia.
        * left. unfold Cn. cbn [meta_slot_cells app].
          destruct (Z_lt_le_dec a (G + 8)) as [B1|B1]; [exists (MCell (LMem (padd g META_prev)) 8 (optr (Some g))); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; fold G; clear - A B1; lia|].
          destruct (Z_lt_le_dec a (G + 16)) as [B2|B2]; [exists (MCell (LMem (padd g META_next)) 8 (optr (Some g))); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; fold G; clear - A B1 B2; lia|].
          destruct (Z_lt_le_dec a (G + 24)) as [B3|B3]; [exists (MCell (LMem (padd g META_mem)) 8 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_mem; fold G; clear - A B2 B3; lia|].
          destruct (Z_lt_le_dec a (G + 28)) as [B4|B4]; [exists (MCell (LMem (padd g META_avail)) 4 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_avail; fold G; clear - A B3 B4; lia|].
          destruct (Z_lt_le_dec a (G + 32)) as [B5|B5]; [exists (MCell (LMem (padd g META_freed)) 4 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_freed; fold G; clear - A B4 B5; lia|].
          exists (MCell (LMem (padd g META_bits)) 8 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_bits; fold G; clear - A B5; lia.
        * left. exists (fmh_cell (Some g)). split; [unfold Cn; apply in_app_iff; right; left; reflexivity|].
          unfold in_rng, cell_range, fmh_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. change (loc_addr L (LCtx CTX_free_meta_head)) with (ly_ctx L + 16).
          rewrite Hctx. clear - A; lia.
    - (* [comment removed for export] *)
      intros c Hc El. set (CH := MCell (LMem (am_mem a4)) 8 (VP g)).
      assert (CHg : In CH (group_cells g a4)) by (left; reflexivity).
      assert (W1 : (1 <= mc_w c)%nat) by exact (image_cell_width s5 c Hc).
      destruct (COV c Hc) as [H1|[H1|H1]].
      + pose proof (REST_vs_gcells L s4 g a4 c CH HK Mg HPW H1 CHg) as D. apply (loc_neq_of_disj L c CH D W1 ltac:(cbn; lia)). exact El.
      + unfold Cn in H1. apply in_app_iff in H1 as [H1|[<-|[]]]; [|discriminate].
        assert (Hgp : In CH (gpart s4)) by (apply (group_in_gpart s4 g a4 CH Mg (proj1 HK)); exact CHg).
        destruct (msc_loc_same g (Some (MFree (Some g) (Some g))) (Some (MUsed a4)) c ltac:(discriminate) ltac:(discriminate) H1) as (c0 & Hc0 & Ec0 & _). apply (front_vs_gpart_loc L s4 c0 CH HPW (msc_in_front s4 g _ c0 HK Mg Hc0) Hgp). rewrite Ec0. exact El.
      + unfold ctx_cells in H1. apply in_app_iff in H1 as [H1|H1].
        * cbn [In] in H1. repeat (destruct H1 as [<-|H1]; [discriminate|]). destruct H1.
        * repeat (apply in_app_iff in H1 as [H1|H1]); apply in_map_iff in H1 as (k & <- & _); discriminate. }
  assert (FR : FRM L s4 sp0 K m m').
  { intros x Hx Hne. destruct (CHG x Hx Hne) as [A|[A|A]].
    - left. clear - A HK1. lia.
    - right. pose proof (In_image_used s4 g a4) as IU.
      destruct (Z_lt_le_dec x (G + 8)) as [B1|B1]; [exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; fold G; clear - A B1; lia|].
      destruct (Z_lt_le_dec x (G + 16)) as [B2|B2]; [exists (MCell (LMem (padd g META_next)) 8 (optr (am_next a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; fold G; clear - A B1 B2; lia|].
      destruct (Z_lt_le_dec x (G + 24)) as [B3|B3]; [exists (MCell (LMem (padd g META_mem)) 8 (VP (am_mem a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_mem; fold G; clear - A B2 B3; lia|].
      destruct (Z_lt_le_dec x (G + 28)) as [B4|B4]; [exists (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_avail; fold G; clear - A B3 B4; lia|].
      destruct (Z_lt_le_dec x (G + 32)) as [B5|B5]; [exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_freed; fold G; clear - A B4 B5; lia|].
      exists (MCell (LMem (padd g META_bits)) 8 (VZ (meta_bits a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_bits; fold G; clear - A B5; lia.
    - right. exists (fmh_cell (st_free_meta_head s4)). split; [apply fmh_cell_in|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range, fmh_cell. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. change (loc_addr L (LCtx CTX_free_meta_head)) with (ly_ctx L + 16).
      rewrite Hctx. clear - A; lia. }
  assert (ZOMB : forall x, In x X -> MT s5 x = MT s4 x).
  { intros x Hx. rewrite Es5. change (MT (set_free_meta_head (Some g) SA) x) with (MT SA x). unfold SA. apply MT_set_other. intros ->. exact (NXg Hx). }
  assert (N5 : NC L X EXC s5 m' sp0 K).
  { apply (NC_next' L _ _ X EXC s4 s5 m m' sp0 K N REPR).
    - intros l Hl. destruct (HEXo l Hl) as (x & b & Hx & Mx & El). exists x, b. split; [exact Hx|]. split; [rewrite ZOMB by exact Hx; exact Mx | exact El].
    - intros x Hx. rewrite ZOMB by exact Hx. exact (HZU x (or_intror Hx)).
    - exact HRS.
    - exact HKs5.
    - exact Hgrow.
    - exact FR.
    - exact Ks5. }
  exists R', m'. split; [exact Hms|]. split.
  { unfold ntf_exit. split; [exact P1|]. split; [exact P2|]. split; [exact P8|]. split; [exact P9|]. split; [exact P18|]. split; [exact P19|].
    split; [exact P10|]. split; [exact P11|]. intros n Hn. apply Poth. clear - Hn. cbn [In] in Hn |- *. tauto. }
  split; [exact (fm0_itree g s4 a4 Mg Hfmh)|]. split; [exact N5|]. split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow | exact FR].
Qed.
End FM0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FM1M.
Variables (m : word -> option byte) (R : bvmap 5 word) (G sp0 BASE LEN canary H HP ra s0 s1 s2 s3 : Z).
Hypothesis Hsp : 2^20 <= sp0 <= 2^47.
Hypothesis HG : 1 <= G /\ G + 40 <= sp0 - 1024.
Hypothesis HH : 1 <= H /\ H + 40 <= sp0 - 1024.
Hypothesis HHP : 1 <= HP /\ HP + 40 <= sp0 - 1024.
Hypothesis DGH : G + 40 <= H \/ H + 40 <= G.
Hypothesis DGP : G + 40 <= HP \/ HP + 40 <= G.
Hypothesis DHP : H = HP \/ H + 40 <= HP \/ HP + 40 <= H.
Let M' := OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1 m R G sp0 BASE LEN canary H HP ra s0 s1 s2 s3.

#[using="Hsp HG HH HHP"] Lemma fm1_out : forall x, 0 <= x < 2^64 -> ~ (sp0 - 88 <= x < sp0 - 48) -> ~ (G <= x < G + 40) -> ~ (H <= x < H + 8) -> ~ (HP + 8 <= x < HP + 16) ->
  M' (wa x) = m (wa x).
Proof. LiaFast.lf_pins (fun (Hsp HG HH HHP : LiaFast.U) => LiaFast.u0). intros x Hx H1 H2 H3 H4. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. do 14 peel. reflexivity. Qed.
#[using="Hsp HG HH HHP DGH DGP DHP"] Lemma fm1_G0 : forall k, (k < 8)%nat -> M' (wa (G + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa HP)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HH HHP DGH DGP DHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. do 2 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HH HHP DGH DGP DHP"] Lemma fm1_G8 : forall k, (k < 8)%nat -> M' (wa (G + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa H)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HH HHP DGH DGP DHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. do 3 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HH HHP DGH DGP DHP"] Lemma fm1_G16 : forall k, (k < 8)%nat -> M' (wa (G + 16 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HH HHP DGH DGP DHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. do 6 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HH HHP DGH DGP DHP"] Lemma fm1_G24 : forall k, (k < 8)%nat -> M' (wa (G + 24 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HH HHP DGH DGP DHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. do 5 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HH HHP DGH DGP DHP"] Lemma fm1_G32 : forall k, (k < 8)%nat -> M' (wa (G + 32 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa 0)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HH HHP DGH DGP DHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. do 4 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HG HH HHP DGH DGP DHP"] Lemma fm1_HP8 : forall k, (k < 8)%nat -> M' (wa (HP + 8 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HG HH HHP DGH DGP DHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. do 1 peel. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Hsp HH HHP"] Lemma fm1_H0 : forall k, (k < 8)%nat -> M' (wa (H + 0 + Z.of_nat k)) = Some (nth k (word_to_le_bytes 8 (wa G)) (Z_to_bv 8 0)).
Proof. LiaFast.lf_pins (fun (Hsp HH HHP : LiaFast.U) => LiaFast.u0). intros k Hk. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. apply wbytes_at_wa; cbn; lia. Qed.
#[using="Type"] Lemma fm1_grows : mem_grows m M'.
Proof. LiaFast.lf_pins LiaFast.u0. unfold M', OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1. repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl. Qed.
End FM1M.

Section FM1.
Context {fx : FPState}.

#[using="Type"] Theorem seg_fm1 : forall L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len h hp hpp hn,
  NC L (g :: X) (LMem (am_mem a4) :: EXC) s4 m sp0 K -> EXC_z X s4 EXC -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa len -> getr R 12 = wa base -> getr R 18 = wa 0x95ed8 ->
  MT s4 g = Some (MUsed a4) -> ~ In g X -> 0 <= base <= 2^64-1 -> 0 <= len <= 2^64-1 ->
  st_free_meta_head s4 = Some h -> h <> g -> hp <> g -> hp <> h ->
  MT s4 h = Some (MFree (Some hp) hn) -> MT s4 hp = Some (MFree hpp (Some h)) ->
  exists R' m', msteps SEGS (mkst R (wa 0x51bb4) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 base len /\
    free_meta g s4 = IRet (tt, s_fm1 s4 g h hp hpp hn) /\ NC L X EXC (s_fm1 s4 g h hp hpp hn) m' sp0 K /\ RS L (s_fm1 s4 g h hp hpp hn) s4 /\
    (forall x, In x X -> MT (s_fm1 s4 g h hp hpp hn) x = MT s4 x) /\ mem_grows m m' /\ FRM L s4 sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len h hp hpp hn N HEXo F R10 R11 R12 R18 Mg NXg Rb Rl Hfmh Hhg Hpg Hph Mh Mhp.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z _ s4 _ (proj1 HK) HEX) as HEO. pose proof HR as (_ & HPW & _).
  assert (Kg : In g (keys s4)) by (eapply MT_keys; exact Mg).
  assert (Kh : In h (keys s4)) by (eapply MT_keys; exact Mh).
  assert (Khp : In hp (keys s4)) by (eapply MT_keys; exact Mhp).
  set (G := loc_addr L (LMem g)) in *. set (H := loc_addr L (LMem h)) in *. set (HP := loc_addr L (LMem hp)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP h Kh) as (H1 & H2 & H3 & H4). destruct (HMP hp Khp) as (P1 & P2' & P3 & P4).
  pose proof (HMD g h Kg Kh (fun E => Hhg (eq_sym E))) as DGH. pose proof (HMD g hp Kg Khp (fun E => Hpg (eq_sym E))) as DGP.
  pose proof (HMD h hp Kh Khp (fun E => Hph (eq_sym E))) as DHP.
  fold G H HP in G1, G2, G3, G4, H1, H2, H3, H4, P1, P2', P3, P4, DGH, DGP, DHP.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_pre R m G sp0 base len canary H HP ra s0 s1 s2 s3).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3; lia); try (clear - Hsp1 HK1; lia).
    all: try (clear - H1 H2 Hsp2 HK1; lia). all: try (clear - P1 P2' Hsp2 HK1; lia). all: try (clear - H2 HK1; lia). all: try (clear - P2' HK1; lia).
    all: try (clear - H3; lia). all: try (clear - P3; lia). all: try (clear - DGH; lia). all: try (clear - DGP; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_fmh L s4 m _ HR HEO Hctx) as E; rewrite Hfmh in E; exact E)
               | (pose proof (rx_fprev L s4 m _ HR HEO HK h _ _ Mh) as E; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s4 m _ HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; replace (H + 0 + d) with (H + d) by ring; apply (rx_msc_wr L s4 m _ HR HEO HK h _ Mh); lia)
               | (intros d n Hd Hn; replace (HP + 8 + d) with (HP + (8 + d)) by ring; apply (rx_msc_wr L s4 m _ HR HEO HK hp _ Mhp); lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_pfm1 R m rom G sp0 base len canary H HP ra s0 s1 s2 s3 P ltac:(constructor)) as (R' & Hms & P1' & P2 & P8 & P9 & P10 & P11 & P12 & P13 & P18 & P19 & Poth).
  set (m' := OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1 m R G sp0 base len canary H HP ra s0 s1 s2 s3) in *.
  set (S1 := set_meta s4 g (MFree (Some hp) (Some h))). set (S2 := set_meta S1 hp (MFree hpp (Some g))).
  assert (Es5 : s_fm1 s4 g h hp hpp hn = set_meta S2 h (MFree (Some g) hn)) by reflexivity.
  set (s5 := s_fm1 s4 g h hp hpp hn) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s4) by (apply keys_set_meta; exact Kg).
  assert (HKS2 : KS S2) by (apply KS_set_meta; [exact HKS1 | rewrite K1; exact Khp]).
  assert (K2 : keys S2 = keys s4) by (unfold S2; rewrite keys_set_meta by (rewrite K1; exact Khp); exact K1).
  assert (HKs5 : KS s5) by (rewrite Es5; apply KS_set_meta; [exact HKS2 | rewrite K2; exact Kh]).
  assert (Ks5 : keys s5 = keys s4) by (rewrite Es5; rewrite keys_set_meta by (rewrite K2; exact Kh); exact K2).
  assert (M5g : MT s5 g = Some (MFree (Some hp) (Some h))) by (rewrite Es5; unfold S2; rewrite !MT_set_other by congruence; unfold S1; apply MT_set_same).
  assert (M5hp : MT s5 hp = Some (MFree hpp (Some g))) by (rewrite Es5; rewrite MT_set_other by congruence; unfold S2; apply MT_set_same).
  assert (M5h : MT s5 h = Some (MFree (Some g) hn)) by (rewrite Es5; apply MT_set_same).
  assert (HRS : RS L s5 s4).
  { rewrite Es5. apply (RS_trans L s4 S2); [apply RS_set_free; [exact HKS2 | rewrite K2; exact Kh]|].
    apply (RS_trans L s4 S1); [apply RS_set_free; [exact HKS1 | rewrite K1; exact Khp]|]. apply RS_set_free; assumption. }
  assert (HGr : 1 <= G /\ G + 40 <= sp0 - 1024) by (clear - G1 G2 HK1; lia).
  assert (HHr : 1 <= H /\ H + 40 <= sp0 - 1024) by (clear - H1 H2 HK1; lia).
  assert (HPr : 1 <= HP /\ HP + 40 <= sp0 - 1024) by (clear - P1 P2' HK1; lia).
  assert (HSP : 2^20 <= sp0 <= 2^47) by (clear - Hsp1 Hsp2 HK1; lia).
  assert (DHP' : H = HP \/ H + 40 <= HP \/ HP + 40 <= H) by (clear - DHP; lia).
  set (CHN := MCell (LMem (padd hp META_next)) 8 (optr (Some g))).
  set (CHP := MCell (LMem (padd h META_prev)) 8 (optr (Some g))).
  set (Cn := meta_slot_cells g (Some (MFree (Some hp) (Some h))) ++ [CHN; CHP]).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) Cn).
  { unfold Cn. cbn [meta_slot_cells app]. repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CHN CHP] in *; rewrite ?loc_padd; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; fold G H HP.
    all: try (clear - HGr HHr HPr HSP; lia).
    all: intros n Hn; unfold m'.
    - apply fm1_G0; assumption.
    - apply fm1_G8; assumption.
    - apply fm1_G16; assumption.
    - rewrite fm1_G24 by (assumption || lia). f_equal. rewrite nth_zero8 by lia. rewrite le4_zero by lia. reflexivity.
    - replace (G + 28 + Z.of_nat n) with (G + 24 + Z.of_nat (n + 4)) by lia. rewrite fm1_G24 by (assumption || lia). f_equal.
      rewrite nth_zero8 by lia. rewrite le4_zero by lia. reflexivity.
    - apply fm1_G32; assumption.
    - apply fm1_HP8; assumption.
    - apply fm1_H0; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply fm1_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (sp0 - 88 <= a < sp0 - 48) \/ (G <= a < G + 40) \/ (H <= a < H + 8) \/ (HP + 8 <= a < HP + 16)).
  { intros a Ra Ha. destruct (decide (sp0 - 88 <= a < sp0 - 48)) as [A1|A1]; [left; exact A1|].
    destruct (decide (G <= a < G + 40)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (H <= a < H + 8)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (HP + 8 <= a < HP + 16)) as [A4|A4]; [right; right; right; exact A4|].
    exfalso. apply Ha. unfold m'. apply fm1_out; assumption. }
  assert (COV : forall c, In c (image s5) -> In c (REST s4 g) \/ In c Cn \/ In c (meta_slot_cells h (Some (MFree (Some hp) hn))) \/
                                             In c (meta_slot_cells hp (Some (MFree hpp (Some h))))).
  { intros c Hc. rewrite Es5 in Hc. destruct (cov_set_free S2 h (Some g) hn c HKS2 ltac:(rewrite K2; exact Kh) Hc) as [H5|H5].
    2:{ destruct (msc_free_links h (Some hp) hn (Some g) hn c H5) as [E|[E|E]]; [right; right; left; exact E | right; left; rewrite E; unfold Cn; apply in_app_iff; right; right; left; reflexivity |].
        right; right; left. rewrite E. cbn [meta_slot_cells]. memb. }
    destruct (cov_set_free S1 hp hpp (Some g) c HKS1 ltac:(rewrite K1; exact Khp) H5) as [H6|H6].
    2:{ destruct (msc_free_links hp hpp (Some h) hpp (Some g) c H6) as [E|[E|E]]; [right; right; right; exact E | right; right; right; rewrite E; cbn [meta_slot_cells]; memb |].
        right; left. rewrite E. unfold Cn. apply in_app_iff. right. left. reflexivity. }
    pose proof (image_set_key s4 g (MFree (Some hp) (Some h)) HK Kg) as PP2.
    change (match MFree (Some hp) (Some h) with MUsed am => group_cells g am | _ => [] end) with (@nil mcell) in PP2. rewrite app_nil_r in PP2.
    apply (Permutation_in c PP2) in H6. apply in_app_iff in H6 as [H6|H6]; [left; exact H6 | right; left; apply in_app_iff; left; exact H6]. }
  assert (REPR : repr_x L s5 (bview SEGS m') EXC).
  { apply (repr_x_drop L s5 _ (LMem (am_mem a4)) EXC).
    - apply (repr_x_next L s4 s5 (bview SEGS m) (bview SEGS m') _ Cn HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
      + intros c Hc. destruct (COV c Hc) as [H1'|[H1'|[H1'|H1']]].
        * left. exact (In_REST_image s4 g c HK Kg H1').
        * right. exact H1'.
        * left. exact (msc_key_in_image s4 h _ c HK Mh H1').
        * left. exact (msc_key_in_image s4 hp _ c HK Mhp H1').
      + intros c Hc. unfold Cn in Hc. apply in_app_iff in Hc as [Hc|[<-|[<-|[]]]].
        * exact (msc_key_in_image s5 g _ c HKs5 M5g Hc).
        * apply (msc_key_in_image s5 hp _ _ HKs5 M5hp). cbn [meta_slot_cells]. memb.
        * apply (msc_key_in_image s5 h _ _ HKs5 M5h). cbn [meta_slot_cells]. memb.
      + exact HNew.
      + intros a Ha. pose proof (bview_ne_range m m' a Ha) as Ra.
        assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
        destruct (CHG a Ra Ha') as [A|[A|[A|A]]].
        * right. intros c Hc _ Hin. destruct (RS_range L s5 s4 c HRS Hc) as (c0 & H0 & E0). pose proof (HC c0 H0) as (Q1 & Q2 & _).
          unfold in_rng, cell_range in Hin. unfold cell_range in E0. injection E0 as E1 E2. rewrite E1 in Q1. rewrite E1, E2 in Q2. cbn [fst snd] in Hin. clear - Hin Q1 Q2 A HK1. lia.
        * left. unfold Cn. cbn [meta_slot_cells app].
          destruct (Z_lt_le_dec a (G + 8)) as [B1|B1]; [exists (MCell (LMem (padd g META_prev)) 8 (optr (Some hp))); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; fold G; clear - A B1; lia|].
          destruct (Z_lt_le_dec a (G + 16)) as [B2|B2]; [exists (MCell (LMem (padd g META_next)) 8 (optr (Some h))); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; fold G; clear - A B1 B2; lia|].
          destruct (Z_lt_le_dec a (G + 24)) as [B3|B3]; [exists (MCell (LMem (padd g META_mem)) 8 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_mem; fold G; clear - A B2 B3; lia|].
          destruct (Z_lt_le_dec a (G + 28)) as [B4|B4]; [exists (MCell (LMem (padd g META_avail)) 4 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_avail; fold G; clear - A B3 B4; lia|].
          destruct (Z_lt_le_dec a (G + 32)) as [B5|B5]; [exists (MCell (LMem (padd g META_freed)) 4 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_freed; fold G; clear - A B4 B5; lia|].
          exists (MCell (LMem (padd g META_bits)) 8 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_bits; fold G; clear - A B5; lia.
        * left. exists CHP. split; [unfold Cn; apply in_app_iff; right; right; left; reflexivity|]. unfold CHP, in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_prev. fold H. clear - A; lia.
        * left. exists CHN. split; [unfold Cn; apply in_app_iff; right; left; reflexivity|]. unfold CHN, in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_next. fold HP. clear - A; lia.
    - intros c Hc El. set (CH := MCell (LMem (am_mem a4)) 8 (VP g)).
      assert (CHg : In CH (group_cells g a4)) by (left; reflexivity).
      assert (Hgp : In CH (gpart s4)) by (apply (group_in_gpart s4 g a4 CH Mg (proj1 HK)); exact CHg).
      assert (W1 : (1 <= mc_w c)%nat) by exact (image_cell_width s5 c Hc).
      destruct (COV c Hc) as [H1'|[H1'|[H1'|H1']]].
      + pose proof (REST_vs_gcells L s4 g a4 c CH HK Mg HPW H1' CHg) as D. apply (loc_neq_of_disj L c CH D W1 ltac:(cbn; lia)). exact El.
      + unfold Cn in H1'. apply in_app_iff in H1' as [H1'|[<-|[<-|[]]]].
        * destruct (msc_loc_same g (Some (MFree (Some hp) (Some h))) (Some (MUsed a4)) c ltac:(discriminate) ltac:(discriminate) H1') as (c0 & Hc0 & Ec0 & _).
          apply (front_vs_gpart_loc L s4 c0 CH HPW (msc_in_front s4 g _ c0 HK Mg Hc0) Hgp). rewrite Ec0. exact El.
        * apply (front_vs_gpart_loc L s4 (MCell (LMem (padd hp META_next)) 8 (optr (Some h))) CH HPW); [apply (msc_in_front s4 hp _ _ HK Mhp); cbn [meta_slot_cells]; memb | exact Hgp | exact El].
        * apply (front_vs_gpart_loc L s4 (MCell (LMem (padd h META_prev)) 8 (optr (Some hp))) CH HPW); [apply (msc_in_front s4 h _ _ HK Mh); cbn [meta_slot_cells]; memb | exact Hgp | exact El].
      + exact (front_vs_gpart_loc L s4 c CH HPW (msc_in_front s4 h _ c HK Mh H1') Hgp El).
      + exact (front_vs_gpart_loc L s4 c CH HPW (msc_in_front s4 hp _ c HK Mhp H1') Hgp El). }
  assert (FR : FRM L s4 sp0 K m m').
  { intros x Hx Hne. destruct (CHG x Hx Hne) as [A|[A|[A|A]]].
    - left. clear - A HK1. lia.
    - right. pose proof (In_image_used s4 g a4) as IU.
      destruct (Z_lt_le_dec x (G + 8)) as [B1|B1]; [exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; fold G; clear - A B1; lia|].
      destruct (Z_lt_le_dec x (G + 16)) as [B2|B2]; [exists (MCell (LMem (padd g META_next)) 8 (optr (am_next a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; fold G; clear - A B1 B2; lia|].
      destruct (Z_lt_le_dec x (G + 24)) as [B3|B3]; [exists (MCell (LMem (padd g META_mem)) 8 (VP (am_mem a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_mem; fold G; clear - A B2 B3; lia|].
      destruct (Z_lt_le_dec x (G + 28)) as [B4|B4]; [exists (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_avail; fold G; clear - A B3 B4; lia|].
      destruct (Z_lt_le_dec x (G + 32)) as [B5|B5]; [exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_freed; fold G; clear - A B4 B5; lia|].
      exists (MCell (LMem (padd g META_bits)) 8 (VZ (meta_bits a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_bits; fold G; clear - A B5; lia.
    - right. exists (MCell (LMem (padd h META_prev)) 8 (optr (Some hp))). split; [apply (msc_key_in_image s4 h _ _ HK Mh); cbn [meta_slot_cells]; memb|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_prev. fold H. clear - A; lia.
    - right. exists (MCell (LMem (padd hp META_next)) 8 (optr (Some h))). split; [apply (msc_key_in_image s4 hp _ _ HK Mhp); cbn [meta_slot_cells]; memb|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_next. fold HP. clear - A; lia. }
  assert (ZOMB : forall x, In x X -> MT s5 x = MT s4 x).
  { intros x Hx. destruct (HZU x (or_intror Hx)) as (ax & Max).
    rewrite Es5. unfold S2, S1. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXg Hx) | intros ->; rewrite Mhp in Max; discriminate | intros ->; rewrite Mh in Max; discriminate]. }
  assert (N5 : NC L X EXC s5 m' sp0 K).
  { apply (NC_next' L _ _ X EXC s4 s5 m m' sp0 K N REPR).
    - intros l Hl. destruct (HEXo l Hl) as (x & b & Hx & Mx & El). exists x, b. split; [exact Hx|]. split; [rewrite ZOMB by exact Hx; exact Mx | exact El].
    - intros x Hx. rewrite ZOMB by exact Hx. exact (HZU x (or_intror Hx)).
    - exact HRS.
    - exact HKs5.
    - exact Hgrow.
    - exact FR.
    - exact Ks5. }
  exists R', m'. split; [exact Hms|]. split.
  { unfold ntf_exit. split; [exact P1'|]. split; [exact P2|]. split; [exact P8|]. split; [exact P9|]. split; [exact P18|]. split; [exact P19|].
    split; [exact P10|]. split; [exact P11|]. intros n Hn. apply Poth. clear - Hn. cbn [In] in Hn |- *. tauto. }
  split; [exact (fm1_itree g s4 a4 Mg h hp hpp hn Hfmh Hhg Hpg Hph Mh Mhp)|]. split; [exact N5|]. split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow | exact FR].
Qed.
End FM1.

Section FM1S.
Context {fx : FPState}.

#[using="Type"] Theorem seg_fm1s : forall L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len h,
  NC L (g :: X) (LMem (am_mem a4) :: EXC) s4 m sp0 K -> EXC_z X s4 EXC -> ntf_frame R m sp0 canary ra s0 s1 s2 s3 ->
  getr R 10 = wa (loc_addr L (LMem g)) -> getr R 11 = wa len -> getr R 12 = wa base -> getr R 18 = wa 0x95ed8 ->
  MT s4 g = Some (MUsed a4) -> ~ In g X -> 0 <= base <= 2^64-1 -> 0 <= len <= 2^64-1 ->
  st_free_meta_head s4 = Some h -> h <> g -> MT s4 h = Some (MFree (Some h) (Some h)) ->
  exists R' m', msteps SEGS (mkst R (wa 0x51bb4) m rom) (mkst R' (wa 0x51ca0) m' rom) /\ ntf_exit R' R ra s0 s1 s2 s3 sp0 base len /\
    free_meta g s4 = IRet (tt, s_fm1s s4 g h) /\ NC L X EXC (s_fm1s s4 g h) m' sp0 K /\ RS L (s_fm1s s4 g h) s4 /\
    (forall x, In x X -> MT (s_fm1s s4 g h) x = MT s4 x) /\ mem_grows m m' /\ FRM L s4 sp0 K m m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L X EXC s4 m R rom sp0 K canary ra s0 s1 s2 s3 g a4 base len h N HEXo F R10 R11 R12 R18 Mg NXg Rb Rl Hfmh Hhg Mh.
  pose proof N as [HR HEX HZU HK Hctx Henv HSTK HK1 Hsp1 Hsp2 Hsp3 HC HMP HMD].
  pose proof (EXC_ok_of_z _ s4 _ (proj1 HK) HEX) as HEO. pose proof HR as (_ & HPW & _).
  assert (Kg : In g (keys s4)) by (eapply MT_keys; exact Mg).
  assert (Kh : In h (keys s4)) by (eapply MT_keys; exact Mh).
  set (G := loc_addr L (LMem g)) in *. set (H := loc_addr L (LMem h)) in *.
  destruct (HMP g Kg) as (G1 & G2 & G3 & G4). destruct (HMP h Kh) as (H1 & H2 & H3 & H4).
  pose proof (HMD g h Kg Kh (fun E => Hhg (eq_sym E))) as DGH.
  fold G H in G1, G2, G3, G4, H1, H2, H3, H4, DGH.
  assert (P : OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_pre R m G sp0 base len canary H H ra s0 s1 s2 s3).
  { pose proof F as [R2 R9 Rsp Asp HSTK1 Rcan Rra Rs0 Rs1 Rs2 Rs3 Mra Ms0 Ms1 Ms2 Ms3 Mcan Mgd].
    constructor; try assumption; try (clear - G1 G2 Hsp2 HK1; lia); try (clear - G2 HK1; lia); try (clear - G3; lia); try (clear - Hsp1 HK1; lia).
    all: try (clear - H1 H2 Hsp2 HK1; lia). all: try (clear - H2 HK1; lia).
    all: try (clear - H3; lia). all: try (clear - DGH; lia).
    all: first [ (rewrite R2; f_equal; ring)
               | (pose proof (rx_fmh L s4 m _ HR HEO Hctx) as E; rewrite Hfmh in E; exact E)
               | (pose proof (rx_fprev L s4 m _ HR HEO HK h _ _ Mh) as E; exact E)
               | (intros d n Hd Hn; replace (G + 0 + d) with (G + d) by ring; apply (rx_msc_wr L s4 m _ HR HEO HK g _ Mg); lia)
               | (intros d n Hd Hn; replace (H + 0 + d) with (H + d) by ring; apply (rx_msc_wr L s4 m _ HR HEO HK h _ Mh); lia)
               | (intros d n Hd Hn; replace (H + 8 + d) with (H + (8 + d)) by ring; apply (rx_msc_wr L s4 m _ HR HEO HK h _ Mh); lia) ]. }
  destruct (OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_pfm1 R m rom G sp0 base len canary H H ra s0 s1 s2 s3 P ltac:(constructor)) as (R' & Hms & P1' & P2 & P8 & P9 & P10 & P11 & P12 & P13 & P18 & P19 & Poth).
  set (m' := OSSVerify.Proofs.fast_float.from_chars.lib.MAX.AXF_dec63z.AXF_fm1z.fm1_mem_pfm1 m R G sp0 base len canary H H ra s0 s1 s2 s3) in *.
  set (S1 := set_meta s4 g (MFree (Some h) (Some h))).
  assert (Es5 : s_fm1s s4 g h = set_meta S1 h (MFree (Some g) (Some g))) by reflexivity.
  set (s5 := s_fm1s s4 g h) in *.
  assert (HKS1 : KS S1) by (apply KS_set_meta; assumption).
  assert (K1 : keys S1 = keys s4) by (apply keys_set_meta; exact Kg).
  assert (HKs5 : KS s5) by (rewrite Es5; apply KS_set_meta; [exact HKS1 | rewrite K1; exact Kh]).
  assert (Ks5 : keys s5 = keys s4) by (rewrite Es5; rewrite keys_set_meta by (rewrite K1; exact Kh); exact K1).
  assert (M5g : MT s5 g = Some (MFree (Some h) (Some h))) by (rewrite Es5; rewrite !MT_set_other by congruence; unfold S1; apply MT_set_same).
  assert (M5h : MT s5 h = Some (MFree (Some g) (Some g))) by (rewrite Es5; apply MT_set_same).
  assert (HRS : RS L s5 s4).
  { rewrite Es5. apply (RS_trans L s4 S1); [apply RS_set_free; [exact HKS1 | rewrite K1; exact Kh]|]. apply RS_set_free; assumption. }
  assert (HGr : 1 <= G /\ G + 40 <= sp0 - 1024) by (clear - G1 G2 HK1; lia).
  assert (HHr : 1 <= H /\ H + 40 <= sp0 - 1024) by (clear - H1 H2 HK1; lia).
  assert (HSP : 2^20 <= sp0 <= 2^47) by (clear - Hsp1 Hsp2 HK1; lia).
  assert (DHP' : H = H \/ H + 40 <= H \/ H + 40 <= H) by (left; reflexivity).
  set (CHN := MCell (LMem (padd h META_next)) 8 (optr (Some g))).
  set (CHP := MCell (LMem (padd h META_prev)) 8 (optr (Some g))).
  set (Cn := meta_slot_cells g (Some (MFree (Some h) (Some h))) ++ [CHN; CHP]).
  assert (HNew : Forall (cell_holds L (bview SEGS m')) Cn).
  { unfold Cn. cbn [meta_slot_cells app]. repeat (first [apply Forall_nil | apply Forall_cons]); apply holds_of_mem.
    all: try (intros z E; discriminate).
    all: try (cbn [mc_w]; clear; lia).
    all: cbn [mc_loc mc_w mc_val sval_num optr CHN CHP] in *; rewrite ?loc_padd; unfold META_prev, META_next, META_mem, META_avail, META_freed, META_bits; fold G H.
    all: try (clear - HGr HHr HSP; lia).
    all: intros n Hn; unfold m'.
    - apply fm1_G0; assumption.
    - apply fm1_G8; assumption.
    - apply fm1_G16; assumption.
    - rewrite fm1_G24 by (assumption || lia). f_equal. rewrite nth_zero8 by lia. rewrite le4_zero by lia. reflexivity.
    - replace (G + 28 + Z.of_nat n) with (G + 24 + Z.of_nat (n + 4)) by lia. rewrite fm1_G24 by (assumption || lia). f_equal.
      rewrite nth_zero8 by lia. rewrite le4_zero by lia. reflexivity.
    - apply fm1_G32; assumption.
    - apply fm1_HP8; assumption.
    - apply fm1_H0; assumption. }
  assert (Hgrow : mem_grows m m') by (unfold m'; apply fm1_grows).
  assert (CHG : forall a, 0 <= a < 2^64 -> m' (wa a) <> m (wa a) -> (sp0 - 88 <= a < sp0 - 48) \/ (G <= a < G + 40) \/ (H <= a < H + 8) \/ (H + 8 <= a < H + 16)).
  { intros a Ra Ha. destruct (decide (sp0 - 88 <= a < sp0 - 48)) as [A1|A1]; [left; exact A1|].
    destruct (decide (G <= a < G + 40)) as [A2|A2]; [right; left; exact A2|].
    destruct (decide (H <= a < H + 8)) as [A3|A3]; [right; right; left; exact A3|].
    destruct (decide (H + 8 <= a < H + 16)) as [A4|A4]; [right; right; right; exact A4|].
    exfalso. apply Ha. unfold m'. apply fm1_out; assumption. }
  assert (COV : forall c, In c (image s5) -> In c (REST s4 g) \/ In c Cn \/ In c (meta_slot_cells h (Some (MFree (Some h) (Some h))))).
  { intros c Hc. rewrite Es5 in Hc. destruct (cov_set_free S1 h (Some g) (Some g) c HKS1 ltac:(rewrite K1; exact Kh) Hc) as [H5|H5].
    2:{ destruct (msc_free_links h (Some h) (Some h) (Some g) (Some g) c H5) as [E|[E|E]]; [right; right; exact E | right; left; rewrite E; unfold Cn; apply in_app_iff; right; right; left; reflexivity |].
        right; left. rewrite E. unfold Cn. apply in_app_iff. right. left. reflexivity. }
    pose proof (image_set_key s4 g (MFree (Some h) (Some h)) HK Kg) as PP2.
    change (match MFree (Some h) (Some h) with MUsed am => group_cells g am | _ => [] end) with (@nil mcell) in PP2. rewrite app_nil_r in PP2.
    apply (Permutation_in c PP2) in H5. apply in_app_iff in H5 as [H5|H5]; [left; exact H5 | right; left; apply in_app_iff; left; exact H5]. }
  assert (REPR : repr_x L s5 (bview SEGS m') EXC).
  { apply (repr_x_drop L s5 _ (LMem (am_mem a4)) EXC).
    - apply (repr_x_next L s4 s5 (bview SEGS m) (bview SEGS m') _ Cn HR eq_refl eq_refl HRS (fun a E => bview_grow_n m m' a Hgrow E)).
      + intros c Hc. destruct (COV c Hc) as [H1'|[H1'|H1']].
        * left. exact (In_REST_image s4 g c HK Kg H1').
        * right. exact H1'.
        * left. exact (msc_key_in_image s4 h _ c HK Mh H1').
      + intros c Hc. unfold Cn in Hc. apply in_app_iff in Hc as [Hc|[<-|[<-|[]]]].
        * exact (msc_key_in_image s5 g _ c HKs5 M5g Hc).
        * apply (msc_key_in_image s5 h _ _ HKs5 M5h). cbn [meta_slot_cells]. memb.
        * apply (msc_key_in_image s5 h _ _ HKs5 M5h). cbn [meta_slot_cells]. memb.
      + exact HNew.
      + intros a Ha. pose proof (bview_ne_range m m' a Ha) as Ra.
        assert (Ha' : m' (wa a) <> m (wa a)) by (intros E; apply Ha; apply bview_ext; exact E).
        destruct (CHG a Ra Ha') as [A|[A|[A|A]]].
        * right. intros c Hc _ Hin. destruct (RS_range L s5 s4 c HRS Hc) as (c0 & H0 & E0). pose proof (HC c0 H0) as (Q1 & Q2 & _).
          unfold in_rng, cell_range in Hin. unfold cell_range in E0. injection E0 as E1 E2. rewrite E1 in Q1. rewrite E1, E2 in Q2. cbn [fst snd] in Hin. clear - Hin Q1 Q2 A HK1. lia.
        * left. unfold Cn. cbn [meta_slot_cells app].
          destruct (Z_lt_le_dec a (G + 8)) as [B1|B1]; [exists (MCell (LMem (padd g META_prev)) 8 (optr (Some h))); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; fold G; clear - A B1; lia|].
          destruct (Z_lt_le_dec a (G + 16)) as [B2|B2]; [exists (MCell (LMem (padd g META_next)) 8 (optr (Some h))); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; fold G; clear - A B1 B2; lia|].
          destruct (Z_lt_le_dec a (G + 24)) as [B3|B3]; [exists (MCell (LMem (padd g META_mem)) 8 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_mem; fold G; clear - A B2 B3; lia|].
          destruct (Z_lt_le_dec a (G + 28)) as [B4|B4]; [exists (MCell (LMem (padd g META_avail)) 4 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_avail; fold G; clear - A B3 B4; lia|].
          destruct (Z_lt_le_dec a (G + 32)) as [B5|B5]; [exists (MCell (LMem (padd g META_freed)) 4 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_freed; fold G; clear - A B4 B5; lia|].
          exists (MCell (LMem (padd g META_bits)) 8 (VZ 0)); split; [memb|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_bits; fold G; clear - A B5; lia.
        * left. exists CHP. split; [unfold Cn; apply in_app_iff; right; right; left; reflexivity|]. unfold CHP, in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_prev. fold H. clear - A; lia.
        * left. exists CHN. split; [unfold Cn; apply in_app_iff; right; left; reflexivity|]. unfold CHN, in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_next. fold H. clear - A; lia.
    - intros c Hc El. set (CH := MCell (LMem (am_mem a4)) 8 (VP g)).
      assert (CHg : In CH (group_cells g a4)) by (left; reflexivity).
      assert (Hgp : In CH (gpart s4)) by (apply (group_in_gpart s4 g a4 CH Mg (proj1 HK)); exact CHg).
      assert (W1 : (1 <= mc_w c)%nat) by exact (image_cell_width s5 c Hc).
      destruct (COV c Hc) as [H1'|[H1'|H1']].
      + pose proof (REST_vs_gcells L s4 g a4 c CH HK Mg HPW H1' CHg) as D. apply (loc_neq_of_disj L c CH D W1 ltac:(cbn; lia)). exact El.
      + unfold Cn in H1'. apply in_app_iff in H1' as [H1'|[<-|[<-|[]]]].
        * destruct (msc_loc_same g (Some (MFree (Some h) (Some h))) (Some (MUsed a4)) c ltac:(discriminate) ltac:(discriminate) H1') as (c0 & Hc0 & Ec0 & _).
          apply (front_vs_gpart_loc L s4 c0 CH HPW (msc_in_front s4 g _ c0 HK Mg Hc0) Hgp). rewrite Ec0. exact El.
        * apply (front_vs_gpart_loc L s4 (MCell (LMem (padd h META_next)) 8 (optr (Some h))) CH HPW); [apply (msc_in_front s4 h _ _ HK Mh); cbn [meta_slot_cells]; memb | exact Hgp | exact El].
        * apply (front_vs_gpart_loc L s4 (MCell (LMem (padd h META_prev)) 8 (optr (Some h))) CH HPW); [apply (msc_in_front s4 h _ _ HK Mh); cbn [meta_slot_cells]; memb | exact Hgp | exact El].
      + exact (front_vs_gpart_loc L s4 c CH HPW (msc_in_front s4 h _ c HK Mh H1') Hgp El). }
  assert (FR : FRM L s4 sp0 K m m').
  { intros x Hx Hne. destruct (CHG x Hx Hne) as [A|[A|[A|A]]].
    - left. clear - A HK1. lia.
    - right. pose proof (In_image_used s4 g a4) as IU.
      destruct (Z_lt_le_dec x (G + 8)) as [B1|B1]; [exists (MCell (LMem (padd g META_prev)) 8 (optr (am_prev a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_prev; fold G; clear - A B1; lia|].
      destruct (Z_lt_le_dec x (G + 16)) as [B2|B2]; [exists (MCell (LMem (padd g META_next)) 8 (optr (am_next a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_next; fold G; clear - A B1 B2; lia|].
      destruct (Z_lt_le_dec x (G + 24)) as [B3|B3]; [exists (MCell (LMem (padd g META_mem)) 8 (VP (am_mem a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_mem; fold G; clear - A B2 B3; lia|].
      destruct (Z_lt_le_dec x (G + 28)) as [B4|B4]; [exists (MCell (LMem (padd g META_avail)) 4 (VZ (am_avail a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_avail; fold G; clear - A B3 B4; lia|].
      destruct (Z_lt_le_dec x (G + 32)) as [B5|B5]; [exists (MCell (LMem (padd g META_freed)) 4 (VZ (am_freed a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_freed; fold G; clear - A B4 B5; lia|].
      exists (MCell (LMem (padd g META_bits)) 8 (VZ (meta_bits a4))); split; [apply (IU _ HK Mg); left; cbn [meta_slot_cells]; memb|]; split; [wide_tac Hctx|]; unfold in_rng, cell_range; cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]; rewrite loc_padd; unfold META_bits; fold G; clear - A B5; lia.
    - right. exists (MCell (LMem (padd h META_prev)) 8 (optr (Some h))). split; [apply (msc_key_in_image s4 h _ _ HK Mh); cbn [meta_slot_cells]; memb|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_prev. fold H. clear - A; lia.
    - right. exists (MCell (LMem (padd h META_next)) 8 (optr (Some h))). split; [apply (msc_key_in_image s4 h _ _ HK Mh); cbn [meta_slot_cells]; memb|]. split; [wide_tac Hctx|].
      unfold in_rng, cell_range. cbn [mc_loc mc_w fst snd Z.of_nat Pos.of_succ_nat]. rewrite loc_padd. unfold META_next. fold H. clear - A; lia. }
  assert (ZOMB : forall x, In x X -> MT s5 x = MT s4 x).
  { intros x Hx. destruct (HZU x (or_intror Hx)) as (ax & Max).
    rewrite Es5. unfold S1. rewrite !MT_set_other; [reflexivity | intros ->; exact (NXg Hx) | intros ->; rewrite Mh in Max; discriminate]. }
  assert (N5 : NC L X EXC s5 m' sp0 K).
  { apply (NC_next' L _ _ X EXC s4 s5 m m' sp0 K N REPR).
    - intros l Hl. destruct (HEXo l Hl) as (x & b & Hx & Mx & El). exists x, b. split; [exact Hx|]. split; [rewrite ZOMB by exact Hx; exact Mx | exact El].
    - intros x Hx. rewrite ZOMB by exact Hx. exact (HZU x (or_intror Hx)).
    - exact HRS.
    - exact HKs5.
    - exact Hgrow.
    - exact FR.
    - exact Ks5. }
  exists R', m'. split; [exact Hms|]. split.
  { unfold ntf_exit. split; [exact P1'|]. split; [exact P2|]. split; [exact P8|]. split; [exact P9|]. split; [exact P18|]. split; [exact P19|].
    split; [exact P10|]. split; [exact P11|]. intros n Hn. apply Poth. clear - Hn. cbn [In] in Hn |- *. tauto. }
  split; [exact (fm1s_itree g s4 a4 Mg h Hfmh Hhg Mh)|]. split; [exact N5|]. split; [exact HRS|]. split; [exact ZOMB|]. split; [exact Hgrow | exact FR].
Qed.
End FM1S.
