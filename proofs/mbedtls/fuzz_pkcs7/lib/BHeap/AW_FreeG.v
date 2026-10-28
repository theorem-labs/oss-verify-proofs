(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX APop AW_FreeP AW_FreeK.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_FreeG () : Init.string Init.list := ["Corelib.Init.Datatypes.nat"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_bl"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hzones"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.d_nb"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.shdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_map_size"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.a_emb"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.zapart"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_T"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctx"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_ctxlen"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_fs"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_pa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_b6"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_lo"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_stk_hi"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.bool"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.from_primary"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.rz_size"; "Stdlib.ZArith.BinInt.Z.max"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.pclass"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.sec_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_chunks'"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_n"; "ARUN_1.ext_lo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_hdr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_user"; "ARUN_1.ext_hi"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kHighMemBeg"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_prim"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_cls"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.carved"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.SH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_map_size"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.needed2"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_rz"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_ab"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.fa_beg"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.l_sb"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FreeK.hgeom"; "ARUN_1.shad"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ri_base"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.alayout"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.blocks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ck_st"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.CHUNK_ALLOCATED"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.nfix"].

Section ARUN_1. Context {hAR : arun}.
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L1483665948.5 L19985763330.500000800@S1A2l11iS1A2l11i". (* [comment removed for export] *)
#[using="Type"] Lemma nth_error_app_r : forall {A} (l1 l2 : list A) i, nth_error (l1 ++ l2) (length l1 + i) = nth_error l2 i.
Proof. intros A l1 l2 i. rewrite nth_error_app2 by lia. f_equal. lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma nth_error_Some_length : forall {A} (l : list A) i x, nth_error l i = Some x -> (i < length l)%nat.
Proof. intros A l i x H. apply (proj1 (nth_error_Some l i)). congruence. Qed.

Section Zones.
  Variable h : ahst.
  Let L := h_L h.
  Hypothesis G : hgeom h.

  Local Ltac fixed i j :=
    exact (G i j _ _ eq_refl eq_refl ltac:(discriminate)).

  #[using="G"] Lemma z_T_ctx : zapart (l_T L, 4096) (l_ctx L, l_ctxlen L). Proof. fixed 0%nat 1%nat. Qed.
  #[using="G"] Lemma z_T_fs : zapart (l_T L, 4096) (l_fs L, kFakeBytes). Proof. fixed 0%nat 2%nat. Qed.
  #[using="G"] Lemma z_T_pa : zapart (l_T L, 4096) (l_pa L, 0x800000). Proof. fixed 0%nat 3%nat. Qed.
  #[using="G"] Lemma z_T_hull : zapart (l_T L, 4096) (l_b6 L, 0x2000011000). Proof. fixed 0%nat 4%nat. Qed.
  #[using="G"] Lemma z_T_stk : zapart (l_T L, 4096) (l_stk_lo L, l_stk_hi L - l_stk_lo L). Proof. fixed 0%nat 5%nat. Qed.
  #[using="G"] Lemma z_T_band : zapart (l_T L, 4096) (0x7fff7000, 0x10007fff8000 - 0x7fff7000). Proof. fixed 0%nat 6%nat. Qed.
  #[using="G"] Lemma z_ctx_hull : zapart (l_ctx L, l_ctxlen L) (l_b6 L, 0x2000011000). Proof. fixed 1%nat 4%nat. Qed.
  #[using="G"] Lemma z_ctx_stk : zapart (l_ctx L, l_ctxlen L) (l_stk_lo L, l_stk_hi L - l_stk_lo L). Proof. fixed 1%nat 5%nat. Qed.
  #[using="G"] Lemma z_ctx_band : zapart (l_ctx L, l_ctxlen L) (0x7fff7000, 0x10007fff8000 - 0x7fff7000). Proof. fixed 1%nat 6%nat. Qed.
  #[using="G"] Lemma z_fs_hull : zapart (l_fs L, kFakeBytes) (l_b6 L, 0x2000011000). Proof. fixed 2%nat 4%nat. Qed.
  #[using="G"] Lemma z_fs_stk : zapart (l_fs L, kFakeBytes) (l_stk_lo L, l_stk_hi L - l_stk_lo L). Proof. fixed 2%nat 5%nat. Qed.
  #[using="G"] Lemma z_fs_band : zapart (l_fs L, kFakeBytes) (0x7fff7000, 0x10007fff8000 - 0x7fff7000). Proof. fixed 2%nat 6%nat. Qed.
  #[using="G"] Lemma z_pa_hull : zapart (l_pa L, 0x800000) (l_b6 L, 0x2000011000). Proof. fixed 3%nat 4%nat. Qed.
  #[using="G"] Lemma z_pa_stk : zapart (l_pa L, 0x800000) (l_stk_lo L, l_stk_hi L - l_stk_lo L). Proof. fixed 3%nat 5%nat. Qed.
  #[using="G"] Lemma z_pa_band : zapart (l_pa L, 0x800000) (0x7fff7000, 0x10007fff8000 - 0x7fff7000). Proof. fixed 3%nat 6%nat. Qed.
  #[using="G"] Lemma z_hull_stk : zapart (l_b6 L, 0x2000011000) (l_stk_lo L, l_stk_hi L - l_stk_lo L). Proof. fixed 4%nat 5%nat. Qed.
  #[using="G"] Lemma z_hull_band : zapart (l_b6 L, 0x2000011000) (0x7fff7000, 0x10007fff8000 - 0x7fff7000). Proof. fixed 4%nat 6%nat. Qed.
  #[using="G"] Lemma z_stk_band : zapart (l_stk_lo L, l_stk_hi L - l_stk_lo L) (0x7fff7000, 0x10007fff8000 - 0x7fff7000). Proof. fixed 5%nat 6%nat. Qed.
  #[using="G"] Lemma z_T_dtls : zapart (l_T L, 4096) (l_dtls L, 4096). Proof. fixed 0%nat 7%nat. Qed.
  #[using="G"] Lemma z_hull_dtls : zapart (l_b6 L, 0x2000011000) (l_dtls L, 4096). Proof. fixed 4%nat 7%nat. Qed.
  #[using="G"] Lemma z_stk_dtls : zapart (l_stk_lo L, l_stk_hi L - l_stk_lo L) (l_dtls L, 4096). Proof. fixed 5%nat 7%nat. Qed.
  #[using="G"] Lemma z_band_dtls : zapart (0x7fff7000, 0x10007fff8000 - 0x7fff7000) (l_dtls L, 4096). Proof. fixed 6%nat 7%nat. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma hzones_node : forall i b, nth_error (d_nb (h_dep h)) i = Some b -> nth_error (hzones h) (8 + i) = Some (b, 2^20).
  Proof.
    intros i b Hi. unfold hzones. cbn [nth_error app Nat.add].
    rewrite nth_error_app1; [rewrite nth_error_map, Hi; reflexivity|]. rewrite length_map. exact (nth_error_Some_length _ _ _ Hi).
  Qed.
  #[using="Type"] Lemma hzones_store : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Pb,$1.P,(2.(3.$1.)(4.$1.(5.(6.Vh,))R2.)(7.$1.R1.))(2.(3.(8.$1.$1.))(4.(8.$1.$1.)(9.Vh,)(:.(:.#8.(;.$1.(<.(6.Vh,))))R3.))(7.(8.$1.$1.)(=.$1.$1.R2.(>.+2.+17.))))")
(* [comment removed for export] *).
  Proof.
    intros i b Hi. unfold hzones. cbn [nth_error app Nat.add].
    rewrite <- (length_map (fun b0 => (b0, 2^20))). rewrite nth_error_app_r.
    rewrite nth_error_app1; [rewrite nth_error_map, Hi; reflexivity|]. rewrite length_map. exact (nth_error_Some_length _ _ _ Hi).
  Qed.
  #[using="Type"] Lemma hzones_sec : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(2.(3.(8.$1.$1.))(4.(8.$1.$1.)(9.Vh,)(:.(:.(:.#8.(;.$1.(<.(6.Vh,))))(;.$1.(5.(6.Vh,))))R3.))(7.(8.$1.$1.)(=.$1.$1.(12.R2.)(13.R2.))))")
(* [comment removed for export] *).
  Proof.
    intros i sh Hi. unfold hzones. cbn [nth_error app Nat.add]. rewrite <- Nat.add_assoc.
    rewrite <- (length_map (fun b0 => (b0, 2^20))). rewrite nth_error_app_r.
    rewrite <- (length_map (fun b0 => (b0, 2^23))). rewrite nth_error_app_r.
    rewrite nth_error_app1; [rewrite nth_error_map, Hi; reflexivity|]. rewrite length_map. exact (nth_error_Some_length _ _ _ Hi).
  Qed.
  (* [comment removed for export] *)
  #[using="Type"] Lemma hzones_emb : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "P,(14.(2.$1.(15.(16.Vh,))=))(2.(3.(8.$1.$1.))(4.(8.$1.$1.)(9.Vh,)(:.(:.(:.#8.(;.$1.(<.(6.Vh,))))(;.$1.(5.(6.Vh,))))(;.$?.(10.(11.Vh,)))))(7.(8.$1.$1.)(=.$1.$1.(15.(16.Vh,))$17.)))")
(* [comment removed for export] *).
  Proof.
    intros NZ. unfold hzones. cbn [nth_error app Nat.add]. rewrite <- Nat.add_assoc.
    rewrite <- (length_map (fun b0 => (b0, 2^20))). rewrite nth_error_app_r.
    rewrite <- (length_map (fun b0 => (b0, 2^23))). rewrite nth_error_app_r.
    rewrite <- (length_map (fun sh => (s_map_beg sh, s_map_size sh)) (s_chunks (h_sec h))) at 1.
    rewrite <- (Nat.add_0_r (length (map _ (s_chunks (h_sec h))))). rewrite nth_error_app_r.
    destruct (Z.eqb_spec (a_emb (h_acct h)) 0) as [E|_]; [exfalso; exact (NZ E)| reflexivity].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L34240400327.9000007S1h1i1H". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_emb : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))P,(14.(2.$1.(15.(16.Vh,))=))(18.(=.$1.$1.(12.R3.)(13.R3.))(=.$1.$1.(15.(16.Vh,))$17.))")
(* [comment removed for export] *).
  Proof.
    intros i sh Hi NZ. apply (G _ _ _ _ (hzones_sec i sh Hi) (hzones_emb NZ)). pose proof (nth_error_Some_length _ _ _ Hi). lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L16449633618.11000008S1f1j2Hf". (* [comment removed for export] *)
  #[using="G"] Lemma z_fixed_dyn : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pf,$0.Pzf,(8.$1.$1.)Pj,$0.Pzd,(8.$1.$1.)P,(19.R4.#8.)P,(2.(3.(8.$1.$1.))(4.(8.$1.$1.)(9.Vh,)R5.)(7.(8.$1.$1.)R4.))P,(2.(3.(8.$1.$1.))(4.(8.$1.$1.)(9.Vh,)(:.#8.R4.))(7.(8.$1.$1.)R3.))(18.R6.R4.)")
(* [comment removed for export] *).
  Proof. intros f zf j zd Hf Zf Zd. exact (G f (8 + j)%nat zf zd Zf Zd ltac:(lia)). Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30226908626.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_T : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(18.(=.$1.$1.(1:.VL,)+1000.)(=.$1.$1.(12.R2.)(13.R2.)))")
(* [comment removed for export] *).
  Proof. intros i sh Hi. eapply (z_fixed_dyn 0 _ (length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + i)%nat); [lia| reflexivity| rewrite <- (hzones_sec i sh Hi); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L11802115489.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_ctx : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(18.(=.$1.$1.(1;.VL,)(1<.VL,))(=.$1.$1.(12.R2.)(13.R2.)))")
(* [comment removed for export] *).
  Proof. intros i sh Hi. eapply (z_fixed_dyn 1 _ (length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + i)%nat); [lia| reflexivity| rewrite <- (hzones_sec i sh Hi); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L64162715952.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_fs : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(18.(=.$1.$1.(1=.VL,)$1>.)(=.$1.$1.(12.R2.)(13.R2.)))")
(* [comment removed for export] *).
  Proof. intros i sh Hi. eapply (z_fixed_dyn 2 _ (length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + i)%nat); [lia| reflexivity| rewrite <- (hzones_sec i sh Hi); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047219.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_pa : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(18.(=.$1.$1.(1?.VL,)+800000.)(=.$1.$1.(12.R2.)(13.R2.)))")
(* [comment removed for export] *).
  Proof. intros i sh Hi. eapply (z_fixed_dyn 3 _ (length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + i)%nat); [lia| reflexivity| rewrite <- (hzones_sec i sh Hi); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047219.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_hull : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(18.(=.$1.$1.(20.VL,)+2000011000.)(=.$1.$1.(12.R2.)(13.R2.)))")
(* [comment removed for export] *).
  Proof. intros i sh Hi. eapply (z_fixed_dyn 4 _ (length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + i)%nat); [lia| reflexivity| rewrite <- (hzones_sec i sh Hi); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047219.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_stk : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(18.(=.$1.$1.(21.VL,)(22.(23.VL,)(21.VL,)))(=.$1.$1.(12.R2.)(13.R2.)))")
(* [comment removed for export] *).
  Proof. intros i sh Hi. eapply (z_fixed_dyn 5 _ (length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + i)%nat); [lia| reflexivity| rewrite <- (hzones_sec i sh Hi); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047219.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_band : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R2.)(7.$?.R1.))(18.(=.$1.$1.+7???7000.(22.+10007???8000.+7???7000.))(=.$1.$1.(12.R2.)(13.R2.)))")
(* [comment removed for export] *).
  Proof. intros i sh Hi. eapply (z_fixed_dyn 6 _ (length (d_nb (h_dep h)) + length (d_bl (h_dep h)) + i)%nat); [lia| reflexivity| rewrite <- (hzones_sec i sh Hi); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L19243456092.1100000:S1h1i1j2NE". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_sec : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Pj,$0.Pshi,$?.Pshj,$?.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R4.)(7.$?.R2.))P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R4.)(7.$?.R2.))P,(14.(2.$0.R6.R5.))(18.(=.$1.$1.(12.R5.)(13.R5.))(=.$1.$1.(12.R4.)(13.R4.)))")
(* [comment removed for export] *).
  Proof. intros i j shi shj Hi Hj NE. eapply G; [exact (hzones_sec i shi Hi)| exact (hzones_sec j shj Hj)| lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L55736367938.1000000:S1h1i1j2Hj". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_node : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.Pj,$0.Pb,$1.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R4.)(7.$?.R3.))P,(2.(3.$1.)(4.$1.(<.(6.Vh,))R3.)(7.$1.R2.))(18.(=.$1.$1.(12.R5.)(13.R5.))(=.$1.$1.R3.(>.+2.+14.)))")
(* [comment removed for export] *).
  Proof. intros i sh j b Hi Hj. eapply G; [exact (hzones_sec i sh Hi)| exact (hzones_node j b Hj)|]. apply nth_error_Some_length in Hj. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L19243352241.1000000:S1h1i1j2Hj". (* [comment removed for export] *)
  #[using="G"] Lemma z_sec_store : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pi,$0.Psh,$?.Pj,$0.Pb,$1.P,(2.(3.$?.)(4.$?.(10.(11.Vh,))R4.)(7.$?.R3.))P,(2.(3.$1.)(4.$1.(5.(6.Vh,))R3.)(7.$1.R2.))(18.(=.$1.$1.(12.R5.)(13.R5.))(=.$1.$1.R3.(>.+2.+17.)))")
(* [comment removed for export] *).
  Proof. intros i sh j b Hi Hj. eapply G; [exact (hzones_sec i sh Hi)| exact (hzones_store j b Hj)|]. apply nth_error_Some_length in Hj. lia. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30226908499.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_node_T : forall j b, nth_error (d_nb (h_dep h)) j = Some b -> zapart (l_T L, 4096) (b, 2^20).
  Proof. intros j b Hj. eapply (z_fixed_dyn 0); [lia| reflexivity| exact (hzones_node j b Hj)]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047090.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_node_hull : forall j b, nth_error (d_nb (h_dep h)) j = Some b -> zapart (l_b6 L, 0x2000011000) (b, 2^20).
  Proof. intros j b Hj. eapply (z_fixed_dyn 4); [lia| reflexivity| exact (hzones_node j b Hj)]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047090.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_node_stk : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pj,$0.Pb,$1.P,(2.(3.$1.)(4.$1.(<.(6.Vh,))R2.)(7.$1.R1.))(18.(=.$1.$1.(21.VL,)(22.(23.VL,)(21.VL,)))(=.$1.$1.R2.(>.+2.+14.)))")
(* [comment removed for export] *).
  Proof. intros j b Hj. eapply (z_fixed_dyn 5); [lia| reflexivity| exact (hzones_node j b Hj)]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047090.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_node_band : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pj,$0.Pb,$1.P,(2.(3.$1.)(4.$1.(<.(6.Vh,))R2.)(7.$1.R1.))(18.(=.$1.$1.+7???7000.(22.+10007???8000.+7???7000.))(=.$1.$1.R2.(>.+2.+14.)))")
(* [comment removed for export] *).
  Proof. intros j b Hj. eapply (z_fixed_dyn 6); [lia| reflexivity| exact (hzones_node j b Hj)]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L30226908499.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_store_T : forall j b, nth_error (d_bl (h_dep h)) j = Some b -> zapart (l_T L, 4096) (b, 2^23).
  Proof. intros j b Hj. eapply (z_fixed_dyn 0 _ (length (d_nb (h_dep h)) + j)%nat); [lia| reflexivity| rewrite <- (hzones_store j b Hj); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047090.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_store_hull : forall j b, nth_error (d_bl (h_dep h)) j = Some b -> zapart (l_b6 L, 0x2000011000) (b, 2^23).
  Proof. intros j b Hj. eapply (z_fixed_dyn 4 _ (length (d_nb (h_dep h)) + j)%nat); [lia| reflexivity| rewrite <- (hzones_store j b Hj); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047090.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_store_stk : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pj,$0.Pb,$1.P,(2.(3.$1.)(4.$1.(5.(6.Vh,))R2.)(7.$1.R1.))(18.(=.$1.$1.(21.VL,)(22.(23.VL,)(21.VL,)))(=.$1.$1.R2.(>.+2.+17.)))")
(* [comment removed for export] *).
  Proof. intros j b Hj. eapply (z_fixed_dyn 5 _ (length (d_nb (h_dep h)) + j)%nat); [lia| reflexivity| rewrite <- (hzones_store j b Hj); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L54441047090.7000001S". (* [comment removed for export] *)
  #[using="G"] Lemma z_store_band : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pj,$0.Pb,$1.P,(2.(3.$1.)(4.$1.(5.(6.Vh,))R2.)(7.$1.R1.))(18.(=.$1.$1.+7???7000.(22.+10007???8000.+7???7000.))(=.$1.$1.R2.(>.+2.+17.)))")
(* [comment removed for export] *).
  Proof. intros j b Hj. eapply (z_fixed_dyn 6 _ (length (d_nb (h_dep h)) + j)%nat); [lia| reflexivity| rewrite <- (hzones_store j b Hj); f_equal; lia]. Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Zones.

(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L19146306265.5L54961752591.300000900?S1c2E12E2S1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma max_count_range : forall c, 1 <= c <= 31 -> 2 <= max_count c <= 16.
Proof.
  intros c Hc.
  pose proof (allz_spec (fun y => (2 <=? max_count y) && (max_count y <=? 16))%bool 1 31 c ltac:(vm_compute; reflexivity) ltac:(lia)) as E.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L45181140153.5L54961752591.300000900?S1c2E12E2S1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma class_size_range : forall c, 1 <= c <= 31 -> 32 <= class_size c <= 65536.
Proof.
  intros c Hc.
  pose proof (allz_spec (fun y => (32 <=? class_size y) && (class_size y <=? 65536))%bool 1 31 c ltac:(vm_compute; reflexivity) ltac:(lia)) as E.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ext_lo (k : chunk) : Z := if ck_prim k then ck_ab k else ck_map_beg k.
Definition ext_hi (k : chunk) : Z := ck_end k.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L17530742435.3L63373994096.2000005006S1n1HS". (* [comment removed for export] *)
#[using="Type"] Lemma rounded_ge : forall n, Z.max n 8 <= rounded n.
Proof. intros n. unfold rounded. pose proof (round_up_spec (Z.max n 8) 8 ltac:(lia)). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L29498246038.6000008S1n2NC1H". (* [comment removed for export] *)
#[using="Type"] Lemma user_end_prim : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pn,$1.P,(24.=R1.)P,(2.$25.(26.R2.)$27.)(28.(24.(29.(2:.R3.)(2;.R3.+8.))(2<.(2=.R3.)))(2>.(2:.R3.)(2<.(2=.R3.))))")
(* [comment removed for export] *).
Proof. intros n Hn FP. pose proof (needed_le_class n Hn FP) as NC. unfold needed in NC. pose proof (rounded_ge n). lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L15663304985.12L36591511435.10L61028779636.9 L61029205878.7 L63368232347.5 L63368316460.11L63368316589.10L63374621462.8 L9706078557.11 00000>00G00J00M00P00S00V00Y00\S1n1H2H02H12H2S1n2NC2H1S1nS1nS1nS1nS1nS1nS1n". (* [comment removed for export] *)
#[using="Type"] Lemma user_end_prim8 : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pn,$1.P,(24.=R1.)P,(2.$25.(26.R2.)$27.)(24.(29.(2?.+8.(30.(29.R3.+7.)+8.))(2:.R3.))(2<.(2=.R3.)))")
(* [comment removed for export] *).
Proof.
  intros n Hn FP. pose proof (needed_le_class n Hn FP) as NC. unfold needed, rounded in NC.
  pose proof (round_up_spec (Z.max n 8) 8 ltac:(lia)) as [R1 R2].
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  assert (8 * ((n + 7) / 8) <= round_up (Z.max n 8) 8); [| lia].
  unfold round_up in *. pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)).
  assert ((n + 7) / 8 <= (Z.max n 8 + 8 - 1) / 8); [apply Z.div_le_mono; lia| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L18928694158.4L7450215772.7 00000100<SS1n1H2H02H1". (* [comment removed for export] *)
#[using="Type"] Lemma user_end_sec : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pn,$1.P,(24.=R1.)P,(2.$25.(26.R2.)$31.)(28.(24.(29.(29.+1000.(2:.R3.))(2;.R3.+8.))(32.R3.))(2>.(29.+1000.(2:.R3.))(32.R3.)))")
(* [comment removed for export] *).
Proof.
  intros n Hn FP. unfold sec_map_size, needed2. rewrite FP. unfold needed.
  pose proof (round_up_spec (rounded n + rz_size n + rz_size n) 4096 ltac:(lia)). pose proof (rounded_ge n). pose proof (rz_size_bound' n). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L18928694158.4L45138917669.700000100<SS1n2FP2R11H". (* [comment removed for export] *)
#[using="Type"] Lemma sec_map_big : forall n, 0 <= n -> from_primary n = false -> 0x10000 + 4096 < sec_map_size n.
Proof.
  intros n Hn FP. unfold sec_map_size, needed2. rewrite FP. unfold from_primary, kMaxSize in FP. apply Z.leb_gt in FP.
  pose proof (round_up_spec (needed n + rz_size n) 4096 ltac:(lia)) as [R1 R2]. pose proof (rz_size_bound' n). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10326435949.5 L17618935810.22L18122135357.22L22047206724.23L26508106876.22L27614394732.3 L30609032103.22L36032746254.25L36436525488.24L3672735891.19 L37328994181.25L3806204887.25 L3806308983.22 L49158730383.17L49158730383.18L49158781337.20L49160453376.25L49160471712.22L55933314122.25L59959278059.4 L6482380940.2  L66010691956.3 00000?00F00P00Y00c01001:01B01K01R01Z01_01f01l02602@02H02R02Z02d02k035S1h1k1i3EAB3KCSS3hAR1kS3hAR1k2RZS1h1k3C30S3hAR1k2UES1k5MBAND3M63S3hAR1k2ULS1h1k2RZS1h1k3CSRS1k3C30S1h1k2ULS1h1kS3hAR1kS1k2WNS3hAR1k2WNS3hAR1k2WNS1h1k2WNS3hAR1k2WNS1h1k2UES1h1k1i2HiS1k3BIGS3hAR1h2WL". (* [comment removed for export] *)
#[using="Type"] Lemma chunk_ext' : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk,$34.P,(35.VhAR,(36.R2.))P,(37.R3.)P,(38.VhAR,R4.)P,(39.$34.R4.(3:.R5.))(28.(24.=(3;.R5.))(28.(24.(3<.R5.)(3=.R5.))(28.(2.$1.(29.(3=.R5.)+10.)(3>.R5.))(28.(24.(29.(3>.R5.)(2;.(3;.R5.)+8.))(3?.R5.))(28.(2>.(3>.R5.)(3?.R5.))(28.(28.(24.+65?000.(3<.R5.))(40.(24.(3?.R5.)+7???7000.)(24.$41.(3<.R5.))))(28.(24.(3?.R5.)(42.VhAR,))(40.(28.(2.$25.(43.R5.)$27.)(28.(28.(24.+1.(44.R5.))(24.(44.R5.)+1>.))(28.(24.(45.(36.R6.)(44.R5.))(3<.R5.))(28.(24.(3?.R5.)(29.(45.(36.R6.)(44.R5.))(46.(47.R6.(44.R5.)))))(48.$1.Li,$1.(28.(28.(24.=R1.)(2>.R1.(49.R7.(44.R6.))))(28.(2.$1.(3<.R6.)(4:.(36.R7.)(44.R6.)R1.))(2.$1.(3?.R6.)(29.(4:.(36.R7.)(44.R6.)R1.)(2<.(44.R6.)))))))))))(28.(2.$25.(43.R5.)$31.)(48.$0.Li,$0.(28.(2.(3.$?.)(4.$?.(10.(11.R7.))R1.)(7.$?.(4;.(4<.R6.)(4=.R6.)(4>.(3;.R6.)))))(28.(2.$1.(3<.R6.)(4<.R6.))(2.$1.(3?.R6.)(29.(4<.R6.)(4=.R6.)))))))))))))))")
(* [comment removed for export] *).
Proof.
  (intros h k WL WR dd_H; ddestruct dd_H as (WKF & _ & _); intros Hk).
  pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & WST & WP & WX).
  unfold ext_lo, ext_hi, ck_end, ck_hdr, ck_user, ck_rz, kChunkHeaderSize. pose proof (rz_size_bound' (ck_n k)) as RZ.
  destruct (ck_prim k) eqn:PK.
  - ddestruct WX as (ECLS & C30 & i & Hi & EAB).
    pose proof (user_end_prim (ck_n k) ltac:(lia) ltac:(symmetry; exact WP)) as [UE UL]. rewrite <- ECLS in UE, UL.
    pose proof (WR (ck_cls k) ltac:(unfold kNumClasses; lia)) as WRc. cbn zeta in WRc.
    ddestruct WRc as (_ & AUMU & AUCS & MUAL & MULIM & _).
    pose proof (class_size_range (ck_cls k) ltac:(lia)) as CSR.
    unfold carved in Hi.
    assert (KCS : i * class_size (ck_cls k) + class_size (ck_cls k) <= r_alloc_user (h_reg h (ck_cls k))).
    { rewrite AUCS in Hi |- *. rewrite Z.mul_comm, Z.div_mul in Hi by lia. nia. }
    unfold wf_L in WL. unfold chunk_at, region_beg, kRegionSize, kUserLimit, kHighMemBeg, space_end, kSpaceSize in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    assert (SBH : 0x10007fff8000 <= l_sb (h_L h)) by (clear - WL; lia).
    split; [split; [clear - SBH EAB Hi CSR C30; nia| right; clear - SBH EAB Hi CSR C30; nia]|]. split; [clear - WL EAB KCS CSR C30 AUMU MULIM; nia|].
    left. split; [reflexivity|]. split; [exact C30|]. split; [clear - EAB Hi CSR; nia|]. split; [clear - EAB KCS; lia|].
    exists i. split; [unfold carved; clear -Hi; lia|]. split; [exact EAB| rewrite EAB; reflexivity].
  - ddestruct WX as (i & NTH & MB4 & MB0 & MBH & MBL).
    pose proof (user_end_sec (ck_n k) ltac:(lia) ltac:(symmetry; exact WP)) as [UE UL].
    pose proof (sec_map_big (ck_n k) ltac:(lia) ltac:(symmetry; exact WP)) as BIG.
    pose proof (lowhigh_big _ _ MBL ltac:(unfold ck_map_size; clear - BIG; lia)) as M63. ddestruct MBL as (_ & _ & MBAND).
    unfold ck_map_beg, ck_map_size in *.
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [clear - M63 MBAND; lia|]. split; [exact MBH|].
    right. split; [reflexivity|]. exists i. split; [exact NTH|]. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L15131189237.20L18928660338.15L22049067773.17L24892865650.13L24893111410.18L25160584442.19L49160816163.13L51249700787.13L58633594135.1600000N00Q00Y00`00e00j01401>01OS1h1k1i3R163D164SB163C162DC2DSS1kS1h1k2WCS3hAR1kS1h1kS1h1kS3hAR1k2WNS3hAR1k2RZS1k2MB3R163D162DM". (* [comment removed for export] *)
#[using="Type"] Lemma chunk_geom' : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk,$34.P,(35.VhAR,(36.R2.))P,(37.R3.)P,(38.VhAR,R4.)P,(39.$34.R4.(3:.R5.))(28.(24.+10.(4?.R5.))(28.(24.=(3;.R5.))(2.$1.(50.(3>.R5.)+8.)=)))")
(* [comment removed for export] *).
Proof.
  (intros h k WL WR dd_H; ddestruct dd_H as (WKF & _ & _); intros Hk).
  pose proof (proj1 (Forall_forall _ _) WKF k Hk) as (WN & WST & WP & WX).
  pose proof (rz_size_bound' (ck_n k)) as RZ. pose proof (rz_size_mod16 (ck_n k)) as R16.
  split; [unfold ck_rz; lia|]. split; [lia|].
  unfold ck_user, ck_rz. pose proof (Z.div_mod (rz_size (ck_n k)) 16 ltac:(lia)) as D16.
  destruct (ck_prim k).
  - ddestruct WX as (_ & WC & i & Hi & ->). unfold chunk_at, region_beg, kRegionSize.
    pose proof WL as (SB16 & _).
    pose proof (class_size_mod16 (ck_cls k) ltac:(lia)) as C16. pose proof (Z.div_mod (class_size (ck_cls k)) 16 ltac:(lia)) as DC.
    pose proof (Z.div_mod (l_sb (h_L h)) (2^16) ltac:(lia)) as DS.
    replace (l_sb (h_L h) + ck_cls k * 2 ^ 32 + i * class_size (ck_cls k) + rz_size (ck_n k))
      with (8 * (l_sb (h_L h) / 2^16 * 2^13 + ck_cls k * 2^29 + i * (class_size (ck_cls k) / 16) * 2 + rz_size (ck_n k) / 16 * 2)) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult.
  - ddestruct WX as (i & _ & MB & _). unfold ck_map_beg in MB. pose proof (Z.div_mod (ck_ab k - 4096) 4096 ltac:(lia)) as DM.
    replace (ck_ab k + rz_size (ck_n k)) with (8 * ((ck_ab k - 4096) / 4096 * 512 + 512 + rz_size (ck_n k) / 16 * 2)) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L18927809613.38L31237512594.34L34616384265.33L39937991334.31L55556370704.35L59314873579.13L61359547756.38L61359549695.38L66867821864.38L8852918445.29 00000m01401;01B01T02902A02I02S02ZS1h2k12k21x2X12X22C12i12I12C22i22I25AUMU15AUMU23CS13CS22NI2LES2k22C2S2k12C1S2k22C2S1h2k12k22i22L12L2S1h2k12k21x2X12X22i12H12i22L21H2L12H2S2k13CS1S2k13CS1S2i12i22LTS2k12C1". (* [comment removed for export] *)
#[using="Type"] Lemma ext_apart_pp : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk1,$34.Pk2,$34.Px,$1.P,(35.VhAR,(36.R4.))P,(37.R5.)P,(38.VhAR,R6.)P,(39.$34.R6.(3:.R7.))P,(39.$34.R6.(3:.R8.))P,(2.$25.(43.R8.)$27.)P,(2.$25.(43.R8.)$27.)P,(14.(2.$1.(51.R:.)(51.R9.)))P,(28.(24.(3<.R;.)R9.)(2>.R9.(3?.R;.)))(14.(28.(24.(3<.R;.)R:.)(2>.R:.(3?.R;.))))")
(* [comment removed for export] *).
Proof.
  intros h k1 k2 x WL WR WK Hk1 Hk2 P1 P2 NE X1 X2.
  ddestruct (chunk_ext' h k1 WL WR WK Hk1) as (_ & _ & _ & _ & _ & _ & _ & [(_ & C1 & R1 & R1' & i1 & I1 & L1 & H1)|(P1' & _)]); [| congruence].
  ddestruct (chunk_ext' h k2 WL WR WK Hk2) as (_ & _ & _ & _ & _ & _ & _ & [(_ & C2 & R2 & R2' & i2 & I2 & L2 & H2)|(P2' & _)]); [| congruence].
  unfold ext_lo in *. rewrite P1 in *. rewrite P2 in *.
  pose proof (WR (ck_cls k1) ltac:(unfold kNumClasses; lia)) as WRa. cbn zeta in WRa. ddestruct WRa as (_ & AUMU1 & _ & _ & MULIM1 & _).
  pose proof (WR (ck_cls k2) ltac:(unfold kNumClasses; lia)) as WRb. cbn zeta in WRb. ddestruct WRb as (_ & AUMU2 & _ & _ & MULIM2 & _).
  pose proof (class_size_range (ck_cls k1) ltac:(lia)) as CS1. pose proof (class_size_range (ck_cls k2) ltac:(lia)) as CS2.
  unfold chunk_at, region_beg, kRegionSize, kUserLimit in *.
  destruct (Z.eq_dec (ck_cls k1) (ck_cls k2)) as [EC|NC].
  - rewrite <- EC in *. assert (NI : i1 <> i2) by (intros ->; apply NE; lia).
    destruct (Z_lt_le_dec i1 i2) as [LT|LE].
    + pose proof (Z.mul_le_mono_nonneg_r (i1 + 1) i2 (class_size (ck_cls k1)) ltac:(lia) ltac:(lia)). clear - H X1 X2 L1 H1 L2 H2. lia.
    + pose proof (Z.mul_le_mono_nonneg_r (i2 + 1) i1 (class_size (ck_cls k1)) ltac:(lia) ltac:(lia)). clear - H X1 X2 L1 H1 L2 H2. lia.
  - clear - NC X1 X2 R1 R1' R2 R2' AUMU1 AUMU2 MULIM1 MULIM2 C1 C2. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L16135297131.13L41370214775.8 00000M00SS3hAR1h1c1x2Hc2Hx5MULIM2B12B5S1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma user_in_hull : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pc,$1.Px,$1.P,(35.VhAR,(36.R3.))P,(37.R4.)P,(28.(24.+1.R4.)(24.R4.+1?.))P,(28.(24.(45.(36.R6.)R5.)R4.)(2>.R4.(29.(45.(36.R6.)R5.)(52.(47.R6.R5.)))))(28.(28.(24.(20.(36.R7.))R5.)(2>.R5.(29.(20.(36.R7.))+2000011000.)))(28.(2>.R5.(53.(36.R7.)R6.))(28.(24.(29.(54.(36.R7.))(>.+2.+20.))R5.)(2>.R5.(29.(54.(36.R7.))(>.+2.+25.))))))")
(* [comment removed for export] *).
Proof.
  intros h c x WL WR Hc Hx. pose proof (WR c ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _ & _ & MULIM & _).
  dpose WL as (_ & B1 & B2 & _ & B3 & B4 & B5 & _).
  unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kUserLimit, space_end, kSpaceSize, kHighMemBeg in *. clear WR WL.
  lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L22556665884.23L34614483208.23L59308876128.25L8852918445.22 00000H00O01501<S1h2k11x2X12R13R1'5AUMU1S2k12C1S1h2k12k21x2X12X22C12L22H25AUMU12HX2ZAS2k12C1". (* [comment removed for export] *)
#[using="Type"] Lemma ext_apart_ps : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk1,$34.Pk2,$34.Px,$1.P,(35.VhAR,(36.R4.))P,(37.R5.)P,(38.VhAR,R6.)P,(55.R7.)P,(39.$34.R7.(3:.R8.))P,(39.$34.R7.(3:.R9.))P,(2.$25.(43.R9.)$27.)P,(2.$25.(43.R9.)$31.)P,(28.(24.(3<.R;.)R9.)(2>.R9.(3?.R;.)))(14.(28.(24.(3<.R;.)R:.)(2>.R:.(3?.R;.))))")
(* [comment removed for export] *).
Proof.
  intros h k1 k2 x WL WR WK G Hk1 Hk2 P1 P2 X1 X2.
  ddestruct (chunk_ext' h k1 WL WR WK Hk1) as (_ & _ & _ & _ & _ & _ & _ & [(_ & C1 & R1 & R1' & _)|(P1' & _)]); [| congruence].
  ddestruct (chunk_ext' h k2 WL WR WK Hk2) as (_ & _ & _ & _ & _ & _ & _ & [(P2' & _)|(_ & i2 & N2 & L2 & H2)]); [congruence|].
  pose proof (WR (ck_cls k1) ltac:(unfold kNumClasses; lia)) as WRa. cbn zeta in WRa. ddestruct WRa as (_ & AUMU1 & _).
  destruct (user_in_hull h (ck_cls k1) x WL WR ltac:(lia) ltac:(lia)) as (HX & _).
  pose proof (z_sec_hull h G i2 _ N2) as ZA. unfold zapart in ZA. cbn in ZA. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L55556278951.23L59308876128.2600000:00aS2k12k22EBS2k12k21x2X12X22i12L12H12i22L22H22NI2ZA". (* [comment removed for export] *)
#[using="Type"] Lemma ext_apart_ss : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk1,$34.Pk2,$34.Px,$1.P,(35.VhAR,(36.R4.))P,(37.R5.)P,(38.VhAR,R6.)P,(55.R7.)P,(39.$34.R7.(3:.R8.))P,(39.$34.R7.(3:.R9.))P,(2.$25.(43.R9.)$31.)P,(2.$25.(43.R9.)$31.)P,(14.(2.$1.(51.R;.)(51.R:.)))P,(28.(24.(3<.R<.)R:.)(2>.R:.(3?.R<.)))(14.(28.(24.(3<.R<.)R;.)(2>.R;.(3?.R<.))))")
(* [comment removed for export] *).
Proof.
  intros h k1 k2 x WL WR WK G Hk1 Hk2 P1 P2 NE X1 X2.
  ddestruct (chunk_ext' h k1 WL WR WK Hk1) as (_ & _ & _ & _ & _ & _ & _ & [(P1' & _)|(_ & i1 & N1 & L1 & H1)]); [congruence|].
  ddestruct (chunk_ext' h k2 WL WR WK Hk2) as (_ & _ & _ & _ & _ & _ & _ & [(P2' & _)|(_ & i2 & N2 & L2 & H2)]); [congruence|].
  destruct (Nat.eq_dec i1 i2) as [E|NI].
  { subst i2. rewrite N1 in N2. injection N2 as EB _ _. apply NE. unfold ck_map_beg in EB. lia. }
  pose proof (z_sec_sec h G i1 i2 _ _ N1 N2 NI) as ZA. unfold zapart in ZA. cbn in ZA. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma ext_apart' : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk1,$34.Pk2,$34.Px,$1.P,(35.VhAR,(36.R4.))P,(37.R5.)P,(38.VhAR,R6.)P,(55.R7.)P,(39.$34.R7.(3:.R8.))P,(39.$34.R7.(3:.R9.))P,(14.(2.$1.(51.R9.)(51.R8.)))P,(28.(24.(3<.R:.)R8.)(2>.R8.(3?.R:.)))(14.(28.(24.(3<.R:.)R9.)(2>.R9.(3?.R:.))))")
(* [comment removed for export] *).
Proof.
  intros h k1 k2 x WL WR WK G Hk1 Hk2 NE X1 X2.
  destruct (ck_prim k1) eqn:P1; destruct (ck_prim k2) eqn:P2.
  - exact (ext_apart_pp h k1 k2 x WL WR WK Hk1 Hk2 P1 P2 NE X1 X2).
  - exact (ext_apart_ps h k1 k2 x WL WR WK G Hk1 Hk2 P1 P2 X1 X2).
  - exact (ext_apart_ps h k2 k1 x WL WR WK G Hk2 Hk1 P2 P1 X2 X1).
  - exact (ext_apart_ss h k1 k2 x WL WR WK G Hk1 Hk2 P1 P2 NE X1 X2).
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L32731197603.19L7424273517.19 00000B00OS2k12k21E2L22U22V2S2k12L12U12V1". (* [comment removed for export] *)
#[using="Type"] Lemma hdr_unique : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk1,$34.Pk2,$34.P,(35.VhAR,(36.R3.))P,(37.R4.)P,(38.VhAR,R5.)P,(55.R6.)P,(39.$34.R6.(3:.R7.))P,(39.$34.R6.(3:.R8.))P,(2.$1.(3=.R8.)(3=.R7.))(2.$34.R9.R8.)")
(* [comment removed for export] *).
Proof.
  intros h k1 k2 WL WR WK G Hk1 Hk2 E. dpose WK as (_ & ND & _).
  destruct (Z.eq_dec (ck_ab k1) (ck_ab k2)) as [EA|NA].
  - revert EA Hk1 Hk2. clear E. intros EA Hk1 Hk2. induction (h_chunks h) as [|x l IH]; [destruct Hk1|]. cbn in ND. inversion ND as [|? ? NI ND']; subst.
    destruct Hk1 as [->|Hk1], Hk2 as [->|Hk2]; [reflexivity| | | exact (IH ND' Hk1 Hk2)].
    + exfalso. apply NI. rewrite EA. apply in_map. exact Hk2.
    + exfalso. apply NI. rewrite <- EA. apply in_map. exact Hk1.
  - exfalso. ddestruct (chunk_ext' h k1 WL WR WK Hk1) as (_ & L1 & U1 & _ & V1 & _). ddestruct (chunk_ext' h k2 WL WR WK Hk2) as (_ & L2 & U2 & _ & V2 & _).
    apply (ext_apart' h k1 k2 (ck_hdr k1) WL WR WK G Hk1 Hk2 NA); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shad (a : Z) : Z := 0x7fff8000 + a / 8.   (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L31240251061.4L63374621462.4000007008S1a1b1HS". (* [comment removed for export] *)
#[using="Type"] Lemma shad_mono : forall a b, a <= b -> shad a <= shad b.
Proof. intros a b H. unfold shad. apply Z.add_le_mono_l. apply Z.div_le_mono; lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L59308579281.19L61028779636.17L61028859718.15L61028859847.14L61029042038.13L63368316589.18L63374621462.1600000U00^00g01001901B01KS1a1n1b1k1x2AP2X12X22DA2DB1H2H02H12H2S1a1n1b1kS1a1n1b1kS1a1n1b1kS1a1n1b1kS1a1n1b1kS1a1n1b1k". (* [comment removed for export] *)
#[using="Type"] Lemma shad_apart : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pa,$1.Pn,$1.Pb,$1.Pk,$1.Px,$1.P,(2.$1.(50.R5.+8.)=)P,(2.$1.(50.R4.+8.)=)P,(24.=R6.)P,(24.=R5.)P,(40.(24.(29.R9.R8.)R7.)(24.(29.R7.R6.)R9.))P,(28.(24.(56.R:.)R6.)(2>.R6.(29.(56.R:.)(30.(29.R9.+7.)+8.))))(14.(28.(24.(56.R9.)R7.)(2>.R7.(29.(56.R9.)(30.(29.R8.+7.)+8.)))))")
(* [comment removed for export] *).
Proof.
  intros a n b k x A8 B8 N0 K0 AP X1 X2. unfold shad in *.
  pose proof (Z.div_mod a 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA. pose proof (Z.div_mod b 8 ltac:(lia)) as DB. rewrite B8, Z.add_0_r in DB.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (k + 7) 8 ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L35331509193.20L47944929751.20L53622352686.2000000R01401VS2k12k22A12A22A32A42B12B22B32B42LTS2k12k22A12A22A32A42B12B22B32B42LTS2k12k22A12A22A32A42B12B22B32B42GE". (* [comment removed for export] *)
#[using="Type"] Lemma ext_disj' : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pk1,$34.Pk2,$34.P,(35.VhAR,(36.R3.))P,(37.R4.)P,(38.VhAR,R5.)P,(55.R6.)P,(39.$34.R6.(3:.R7.))P,(39.$34.R6.(3:.R8.))P,(14.(2.$1.(51.R8.)(51.R7.)))(40.(24.(3?.R9.)(3<.R8.))(24.(3?.R8.)(3<.R9.)))")
(* [comment removed for export] *).
Proof.
  intros h k1 k2 WL WR WK G Hk1 Hk2 NE.
  ddestruct (chunk_ext' h k1 WL WR WK Hk1) as (_ & A1 & A2 & A3 & A4 & _). ddestruct (chunk_ext' h k2 WL WR WK Hk2) as (_ & B1 & B2 & B3 & B4 & _).
  destruct (Z_lt_le_dec (Z.max (ext_lo k1) (ext_lo k2)) (Z.min (ext_hi k1) (ext_hi k2))) as [LT|GE]; [| lia].
  exfalso. apply (ext_apart' h k1 k2 (Z.max (ext_lo k1) (ext_lo k2)) WL WR WK G Hk1 Hk2 NE); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L17670928123.8L51322266494.700000600>S1c2c'S2c'3Hc'". (* [comment removed for export] *)
#[using="Type"] Lemma user_vs_fa : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pc,$1.Pc',$1.P,(37.R3.)P,(28.(24.+1.R3.)(24.R3.+1?.))P,(28.(24.+1.R3.)(24.R3.+1?.))(40.(24.(29.(45.(36.R6.)R4.)(52.(47.R6.R4.)))(53.(36.R6.)R5.))(24.(29.(53.(36.R6.)R5.)$57.)(45.(36.R6.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros h c c' WR Hc Hc'. pose proof (WR c' ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _ & _ & MULIM & _).
  unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kUserLimit, kFreeArraySize in *. clear WR.
  assert (c' <= c \/ c + 1 <= c') as [LE|GT] by lia; [left; nia| right; nia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L14085048717.13L51322266494.6 00000K00SS3hAR1h2c'5MULIM2B12B21H2H0S2c'3Hc'". (* [comment removed for export] *)
#[using="Type"] Lemma user_vs_ri : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pc',$1.P,(35.VhAR,(36.R2.))P,(37.R3.)P,(28.(24.+1.R3.)(24.R3.+1?.))(28.(24.(29.(45.(36.R5.)R4.)(52.(47.R5.R4.)))(58.(36.R5.)))(28.(24.(20.(36.R5.))(45.(36.R5.)R4.))(28.(24.(29.(53.(36.R5.)R4.)$57.)(58.(36.R5.)))(24.(29.(58.(36.R5.))+1000.)(29.(20.(36.R5.))+2000011000.)))))")
(* [comment removed for export] *).
Proof.
  intros h c' WL WR Hc'. pose proof (WR c' ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _ & _ & MULIM & _).
  dpose WL as (_ & B1 & B2 & _ & B3 & B4 & B5 & _).
  unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kUserLimit, kFreeArraySize, ri_base, space_end, kSpaceSize, kHighMemBeg in *. clear WR WL.
  assert (c' * 4294967296 <= 31 * 4294967296) by nia. assert (1 * 4294967296 <= c' * 4294967296) by nia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L41359653632.10L4202467691.11 L51324269136.8 00000600S00[S1c2HcS1h1c2c'2Hc3Hc'2NE4AUMU5AUMU2S2c'3Hc'". (* [comment removed for export] *)
#[using="Type"] Lemma user_vs_user : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pc,$1.Pc',$1.P,(37.R3.)P,(28.(24.+1.R3.)(24.R3.+1?.))P,(28.(24.+1.R3.)(24.R3.+1?.))P,(14.(2.$1.R5.R4.))(40.(24.(29.(45.(36.R7.)R5.)(52.(47.R7.R5.)))(45.(36.R7.)R6.))(24.(29.(45.(36.R7.)R6.)(52.(47.R7.R6.)))(45.(36.R7.)R5.)))")
(* [comment removed for export] *).
Proof.
  intros h c c' WR Hc Hc' NE.
  pose proof (WR c' ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _ & _ & MULIM & _).
  pose proof (WR c ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU2 & _ & _ & MULIM2 & _).
  unfold region_beg, kRegionSize, kUserLimit in *. clear WR.
  assert (c' + 1 <= c \/ c + 1 <= c') as [LE|GT] by lia; [left; nia| right; nia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L50625696509.16L61028779636.14L61028859718.12L61028859847.11L61028906580.10L63368316589.15L63374621462.1300000M00T00Y00^00c00l013S1a1n1b1k2AP2DA2DB1H2H02H12H2S1a1n1bS1a1bS1a1bS1a1bS1a1n1b1kS1a1n1b". (* [comment removed for export] *)
#[using="Type"] Lemma shad_disj : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pa,$1.Pn,$1.Pb,$1.Pk,$1.P,(2.$1.(50.R4.+8.)=)P,(2.$1.(50.R3.+8.)=)P,(24.=R5.)P,(24.=R4.)P,(40.(24.(29.R8.R7.)R6.)(24.(29.R6.R5.)R8.))(40.(24.(29.(56.R9.)(30.(29.R8.+7.)+8.))(56.R7.))(24.(29.(56.R7.)(30.(29.R6.+7.)+8.))(56.R9.)))")
(* [comment removed for export] *).
Proof.
  intros a n b k A8 B8 N0 K0 AP. unfold shad.
  pose proof (Z.div_mod a 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA. pose proof (Z.div_mod b 8 ltac:(lia)) as DB. rewrite B8, Z.add_0_r in DB.
  pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod (k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (k + 7) 8 ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L50625696509.15L61028779636.13L61028859718.11L61028859847.10L61028906580.9 L63368316589.14L63374621462.1200000M00T00Y00^00c00l013S1a1n1b1k2AP2DA2DB1H2H02H12H2S1a1n1bS1a1bS1a1bS1a1bS1a1n1b1kS1a1n1b". (* [comment removed for export] *)
#[using="Type"] Lemma shad_disj_gen : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Pa,$1.Pn,$1.Pb,$1.Pk,$1.P,(2.$1.(50.R4.+8.)=)P,(2.$1.(50.R3.+8.)=)P,(24.=R3.)P,(40.(24.(29.R7.R6.)R5.)(24.(29.R5.R4.)R7.))(40.(24.(29.(56.R8.)(30.R7.+8.))(56.R6.))(24.(29.(56.R6.)(30.(29.R5.+7.)+8.))(56.R8.)))")
(* [comment removed for export] *).
Proof.
  intros a n b k A8 B8 K0 AP. unfold shad.
  pose proof (Z.div_mod a 8 ltac:(lia)) as DA. rewrite A8, Z.add_0_r in DA. pose proof (Z.div_mod b 8 ltac:(lia)) as DB. rewrite B8, Z.add_0_r in DB.
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
  pose proof (Z.div_mod (k + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (k + 7) 8 ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L13716438217.6L13716616538.6L4210841438.5 00000;00F00OS1L1c2c'2LES1L1c2c'2GTS1c2c'2NE". (* [comment removed for export] *)
#[using="Type"] Lemma fa_vs_fa : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "PL,$59.Pc,$1.Pc',$1.P,(14.(2.$1.R2.R1.))(40.(24.(29.(53.R4.R2.)$57.)(53.R4.R3.))(24.(29.(53.R4.R3.)$57.)(53.R4.R2.)))")
(* [comment removed for export] *).
Proof.
  intros L c c' NE. unfold fa_beg, region_beg, kRegionSize, kFreeArrayOffset, kFreeArraySize.
  assert (c' + 1 <= c \/ c + 1 <= c') as [LE|GT] by lia; [left| right]; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L25158645705.5L51421597986.6000003008S1LS1L1c". (* [comment removed for export] *)
#[using="Type"] Lemma region_beg16 : forall L c, wf_L L -> region_beg L c mod 16 = 0.
Proof.
  intros L c WL. pose proof WL as (M16 & _). unfold region_beg, kRegionSize.
  pose proof (Z.div_mod (l_sb L) (2^16) ltac:(lia)) as D. rewrite M16, Z.add_0_r in D. rewrite D.
  replace (2 ^ 16 * (l_sb L / 2 ^ 16) + c * 2 ^ 32) with ((2^12 * (l_sb L / 2^16) + c * 2^28) * 16) by lia. apply Z_mod_mult.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L24817243116.10L24891063415.9 L24893111410.8 00000700<00AS1L1c1iS1L1cS1L1c". (* [comment removed for export] *)
#[using="Type"] Lemma chunk_at8 : forall L c i, wf_L L -> 1 <= c <= 31 -> chunk_at L c i mod 8 = 0.
Proof.
  intros L c i WL Hc. unfold chunk_at. pose proof (region_beg16 L c WL) as R16. pose proof (class_size_mod16 c Hc) as C16.
  pose proof (Z.div_mod (region_beg L c) 16 ltac:(lia)) as D1. rewrite R16, Z.add_0_r in D1.
  pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D2. rewrite C16, Z.add_0_r in D2.
  rewrite D1, D2. replace (16 * (region_beg L c / 16) + i * (16 * (class_size c / 16))) with (8 * (2 * (region_beg L c / 16) + i * (class_size c / 16) * 2)) by lia.
  rewrite Z.mul_comm. apply Z_mod_mult.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L30051052623.7L41370218474.600000500;S1h1cS1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma carve_end8 : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pc,$1.P,(35.VhAR,(36.R2.))P,(37.R3.)P,(28.(24.+1.R3.)(24.R3.+1?.))(2.$1.(50.(29.(45.(36.R5.)R4.)(46.(47.R5.R4.)))+8.)=)")
(* [comment removed for export] *).
Proof.
  intros h c WL WR Hc. pose proof (WR c ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & _ & AUCS & _).
  rewrite AUCS. replace (region_beg (h_L h) c + class_size c * carved h c) with (chunk_at (h_L h) c (carved h c)) by (unfold chunk_at; lia).
  apply chunk_at8; [exact WL| exact Hc].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L19325175423.10L26161618168.10L41370216676.7 00000700A00GS1c3CSRS1h1c1i2HiS1c2Hc". (* [comment removed for export] *)
#[using="Type"] Lemma slot_le : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pc,$1.Pi,$1.P,(37.R3.)P,(28.(24.+1.R3.)(24.R3.+1?.))P,(28.(24.=R3.)(2>.R3.(49.R5.R4.)))(28.(24.(45.(36.R6.)R5.)(4:.(36.R6.)R5.R4.))(24.(29.(4:.(36.R6.)R5.R4.)(2<.R5.))(29.(45.(36.R6.)R5.)(46.(47.R6.R5.)))))")
(* [comment removed for export] *).
Proof.
  intros h c i WR Hc Hi. pose proof (WR c ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & AUCS & _).
  pose proof (class_size_range c Hc) as CSR. unfold chunk_at.
  pose proof (Z.mul_le_mono_nonneg_r (i + 1) (carved h c) (class_size c) ltac:(lia) ltac:(lia)). nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma blocks_In : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.PB,$1.PN,$1.P,(39.(8.$1.$1.)(=.$1.$1.R2.R1.)(5:.R3.))(48.$34.Lkb,$34.(28.(39.$34.R1.(3:.R5.))(28.(2.$1.(5;.R1.)$5<.)(28.(2.$1.R4.(3>.R1.))(2.$1.R3.(3;.R1.))))))")
(* [comment removed for export] *).
Proof.
  intros h B N HB. unfold blocks, live in HB. apply in_map_iff in HB. ddestruct HB as (kb & E & Hkb). apply filter_In in Hkb as [Hkb ST].
  apply Z.eqb_eq in ST. exists kb. injection E as E1 E2. repeat split; auto.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L17874144404.17L38008555972.17L47622161505.17L63993029507.1700000700A00P00\S2kb2F3S2kb2F12F2S1a2kb2Ha2F12F2S1a2kb2Ha2F3". (* [comment removed for export] *)
#[using="Type"] Lemma in_blk_chunk : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pa,$1.PB,$1.PN,$1.P,(35.VhAR,(36.R4.))P,(37.R5.)P,(38.VhAR,R6.)P,(39.(8.$1.$1.)(=.$1.$1.R5.R4.)(5:.R7.))P,(28.(24.R6.R7.)(2>.R7.(29.R6.R5.)))(48.$34.Lkb,$34.(28.(39.$34.R1.(3:.R:.))(28.(2.$1.(5;.R1.)$5<.)(28.(2.$1.R8.(3>.R1.))(28.(2.$1.R7.(3;.R1.))(28.(28.(24.(3<.R1.)R9.)(2>.R9.(3?.R1.)))(28.(2.$1.(50.(3>.R1.)+8.)=)(28.(24.(3<.R1.)(3>.R1.))(24.(29.(3>.R1.)(5=.(3;.R1.)))(3?.R1.))))))))))")
(* [comment removed for export] *).
Proof.
  intros h a B N WL WR WK HB Ha. ddestruct (blocks_In h B N HB) as (kb & Hkb & ST & -> & ->).
  ddestruct (chunk_ext' h kb WL WR WK Hkb) as (N0 & F1 & F2 & F3 & F4 & _). ddestruct (chunk_geom' h kb WL WR WK Hkb) as (_ & _ & U8).
  exists kb. unfold nfix. repeat split; auto; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L10757754013.11L17277336569.12L60532867415.12L64744114895.1200000600<00G00MS2kb1CS2kb1CS1h2kb4AUMUS2kb1C". (* [comment removed for export] *)
#[using="Type"] Lemma ext_cases : ltac2:(CDefT.buildp (gd_tbl_AW_FreeG ()) "Ph,$33.Pkb,$34.P,(35.VhAR,(36.R2.))P,(37.R3.)P,(38.VhAR,R4.)P,(39.$34.R4.(3:.R5.))(40.(48.$1.Lc',$1.(28.(2.$25.(43.R6.)$27.)(28.(2.$1.(44.R6.)R1.)(28.(28.(24.+1.R1.)(24.R1.+1>.))(28.(24.(45.(36.R7.)R1.)(3<.R6.))(28.(24.(3?.R6.)(29.(45.(36.R7.)R1.)(46.(47.R7.R1.))))(24.(46.(47.R7.R1.))(52.(47.R7.R1.)))))))))(48.$0.Li,$0.(48.$?.Lsh,$?.(28.(2.$25.(43.R7.)$31.)(28.(2.(3.$?.)(4.$?.(10.(11.R8.))R2.)(7.$?.R1.))(28.(2.$1.(12.R1.)(3<.R7.))(2.$1.(29.(12.R1.)(13.R1.))(3?.R7.))))))))")
(* [comment removed for export] *).
Proof.
  intros h kb WL WR WK Hkb.
  ddestruct (chunk_ext' h kb WL WR WK Hkb) as (_ & _ & _ & _ & _ & _ & _ & [(P & C & RL & RH & _)|(P & i & N & EL & EH)]).
  - left. exists (ck_cls kb). pose proof (WR (ck_cls kb) ltac:(unfold kNumClasses; lia)) as W. cbn zeta in W. ddestruct W as (_ & AUMU & _).
    repeat split; auto; lia.
  - right. dexists i, (SH (ck_map_beg kb) (ck_map_size kb) (needed2 (ck_n kb))). cbn. repeat split; auto; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

End ARUN_1.
