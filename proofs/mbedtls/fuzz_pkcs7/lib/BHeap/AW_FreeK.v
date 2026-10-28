(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Madvise.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX AW_FreeP. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv AKinvM.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AW_FreeK () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kNumClasses"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.region0"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_alloc_user"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_user"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kUserLimit"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_mapped_fa"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArrayMapSize"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFreeArraySize"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.r_nfreed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_L'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_L"; "ARUN_1.wfk_region"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_depot'"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.wf_budget"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_big"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.wf_ghost"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.AVOL_MAX"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "ARUN_1.hzones"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Logic.not"; "ARUN_1.zapart"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
Definition wfk_region (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeK ()) "Pc,$0.P,(1.(2.=R1.)(3.R1.$4.))Zr,$5.(6.O1.R2.)(1.P,(7.$0.R3.=)(7.$5.R2.$8.)(1.(1.(2.=(9.R1.))(2.(9.R1.)(:.R1.)))(1.(7.$0.(;.(:.R1.)$<.)=)(1.(2.(:.R1.)$=.)(1.(7.$0.(;.(>.R1.)$?.)=)(1.(1.(2.=(>.R1.))(2.(>.R1.)$10.))(2.(11.+4.(12.R1.))(>.R1.))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)

Definition WFK (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeK ()) "(1.(13.VhAR,(14.O1.))(1.(15.O1.)(1.(16.O1.)(1.(17.VhAR,O1.)(1.(18.VhAR,O1.)(1.(19.O1.)(1.(1:.VhAR,O1.)(2.(1;.O1.)$1<.))))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma WFK_of_awf' : forall h, awf' h -> h_havol h <= AVOL_MAX -> WFK h.
Proof.
  (intros h dd_H; ddestruct dd_H as (WL & WC & WR & WK & WQ & WS & WD & WB & WBIG & WX & WG); intros HV). destruct WX as [WX1 WX2].
  split; [exact WL|]. split; [| exact (conj WS (conj WD (conj WB (conj WBIG (conj WG HV)))))].
  intros c Hc. pose proof (WR c Hc) as R. cbn zeta in R. ddestruct R as (R0 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & _).
  cbn zeta. split; [exact R0|]. split; [exact R1|]. split; [exact R3|]. split; [exact R4|]. split; [exact R6|]. split; [exact R7| exact R8].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition faa (h : ahst) (c : Z) : Z := fa_beg (h_L h) c + r_mapped_fa (h_reg h c).
Definition uaa (h : ahst) (c : Z) : Z := region_beg (h_L h) c + r_mapped_user (h_reg h c).
Definition hdep (h : ahst) (nb bl : list Z) : ahst := set_dep h (DP (d_n (h_dep h)) nb (s_total (h_dep h)) bl).

(* [comment removed for export] *)
Definition shpb (beg : Z) : Z := (0x7fff8000 + beg / 8 + 4095) / 4096 * 4096.
Definition shpe (beg size : Z) : Z := (0x7fff8000 + beg / 8 + size / 8) / 4096 * 4096.

(* [comment removed for export] *)
Definition hzones (h : ahst) : list (Z * Z) :=
  let L := h_L h in
  [(l_T L, 4096); (l_ctx L, l_ctxlen L); (l_fs L, kFakeBytes); (l_pa L, 0x800000); (l_b6 L, 0x2000011000); (l_stk_lo L, l_stk_hi L - l_stk_lo L);
   (0x7fff7000, 0x10007fff8000 - 0x7fff7000) (* [comment removed for export] *); (l_dtls L, 4096)]
  ++ map (fun b => (b, 2^20)) (d_nb (h_dep h)) ++ map (fun b => (b, 2^23)) (d_bl (h_dep h))
  ++ map (fun sh => (s_map_beg sh, s_map_size sh)) (s_chunks (h_sec h))
  (* [comment removed for export] *)
  ++ (if a_emb (h_acct h) =? 0 then [] else [(a_emb (h_acct h), kEmbBytes)]).
Definition zapart (z z' : Z * Z) : Prop := fst z + snd z <= fst z' \/ fst z' + snd z' <= fst z.
Definition hgeom (h : ahst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_FreeK ()) "Pi,$1=.Pj,$1=.Pz,(1>.$0.$0.)Pz',(1>.$0.$0.)P,(7.(1?.(1>.$0.$0.))(20.(1>.$0.$0.)(21.O1.)R4.)(22.(1>.$0.$0.)R2.))P,(7.(1?.(1>.$0.$0.))(20.(1>.$0.$0.)(21.O1.)R4.)(22.(1>.$0.$0.)R2.))P,(23.(7.$1=.R6.R5.))(24.R5.R4.)")
(* [comment removed for export] *).

Record ffam (AL : asan_layout) := FF {
  ff_CS : ahst -> Z -> Prop;
  ff_K : ahst -> Model -> Prop;
  (* [comment removed for export] *)
  ff_csok : forall h, cs_ok AL (ff_CS h);
  ff_kinv : forall h, kinv AL (ff_CS h) (ff_K h);
  ff_view_K : forall h h' mo, kview_eq h h' -> ff_K h mo -> ff_K h' mo;
  ff_view_CS : forall h h' x, kview_eq h h' -> ff_CS h x -> ff_CS h' x;
  ff_noshadow : forall h x, ff_CS h x -> ~ (0x7fff8000 <= x < 0x10007fff8000);
  ff_halted : forall h mo, ff_K h mo -> m_halted mo = None;
  ff_geom : forall h mo, WFK h -> ff_K h mo -> hgeom h;
  (* [comment removed for export] *)
  ff_apart : forall h mo (a n : word), ff_K h mo ->
      region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a n = true ->
      0x10000 <= bv_unsigned n -> bv_unsigned a + bv_unsigned n <= ACEIL ->
      forall x, (ff_CS h x \/ al_img_lo AL <= x < al_img_hi AL) -> ~ (bv_unsigned a <= x < bv_unsigned a + bv_unsigned n);
  (* [comment removed for export] *)
  ff_cs_T : forall h, WFK h -> crange (ff_CS h) (l_T (h_L h)) 4096;
  ff_cs_ctx : forall h, WFK h -> crange (ff_CS h) (l_ctx (h_L h)) (l_ctxlen (h_L h));
  ff_cs_ri : forall h, WFK h -> crange (ff_CS h) (ri_base (h_L h)) 4096;
  ff_cs_fs : forall h, WFK h -> crange (ff_CS h) (l_fs (h_L h)) kFakeBytes;
  ff_cs_stack : forall h lo n, WFK h -> l_stk_lo (h_L h) <= lo -> lo + n <= l_stk_hi (h_L h) -> crange (ff_CS h) lo n;
  ff_cs_user : forall h c, WFK h -> 1 <= c <= 31 -> crange (ff_CS h) (region_beg (h_L h) c) (r_mapped_user (h_reg h c));
  ff_cs_fa : forall h c, WFK h -> 1 <= c <= 31 -> crange (ff_CS h) (fa_beg (h_L h) c) (r_mapped_fa (h_reg h c));
  ff_cs_node : forall h mo b, ff_K h mo -> In b (d_nb (h_dep h)) -> crange (ff_CS h) b (2^20);
  ff_cs_store : forall h mo b, ff_K h mo -> In b (d_bl (h_dep h)) -> crange (ff_CS h) b (2^23);
  ff_cs_sec : forall h mo sh, ff_K h mo -> In sh (s_chunks (h_sec h)) -> crange (ff_CS h) (s_map_beg sh) (s_map_size sh);
  ff_cs_pa : forall h, WFK h -> crange (ff_CS h) (l_pa (h_L h)) (h_pa_committed h);
  ff_cs_img : forall h a n, WFK h -> al_img_lo AL <= a -> a + n <= al_img_hi AL ->
      (a + n <= al_got AL - 63 \/ al_got AL + 64 <= a) -> (a + n <= al_gsb AL - 63 \/ al_gsb AL + 64 <= a) -> crange (ff_CS h) a n;
  (* [comment removed for export] *)
  ff_fa_ledger : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize -> ff_K h mo ->
      region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 (faa h c)) (Z_to_bv 64 (2^18)) = true
      /\ (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 (faa h c)) (Z_to_bv 64 (2^18)) = true
          \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 (faa h c)) (Z_to_bv 64 (2^18)) = true);
  ff_fa_commit : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize -> ff_K h mo ->
      map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 (faa h c)) (Z_to_bv 64 (2^18)) = true ->
      ff_K (h_fagrow h c) (fixrw_commit 0x32 (faa h c) (2^18) mo);
  ff_fa_fresh : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize -> ff_K h mo ->
      region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 (faa h c)) (Z_to_bv 64 (2^18)) = true ->
      ff_K (h_fagrow h c) (fixrw_fresh 0x32 (faa h c) (2^18) mo);
  ff_fa_room : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize -> ff_K h mo ->
      fixrw_grantable 0x32 (faa h c) (2^18) mo;
  (* [comment removed for export] *)
  ff_fa_scar : forall h c, WFK h -> 1 <= c <= 31 -> r_mapped_fa (h_reg h c) + kFreeArrayMapSize <= kFreeArraySize ->
      scar_site AL (ff_CS h) (ff_K h) (faa h c) (2^18);
  (* [comment removed for export] *)
  ff_u_ledger : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_user (h_reg h c) + kUserMapSize <= kUserLimit -> ff_K h mo ->
      region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 (uaa h c)) (Z_to_bv 64 (2^18)) = true
      /\ (map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 (uaa h c)) (Z_to_bv 64 (2^18)) = true
          \/ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 (uaa h c)) (Z_to_bv 64 (2^18)) = true);
  ff_u_commit : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_user (h_reg h c) + kUserMapSize <= kUserLimit -> ff_K h mo ->
      map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 (uaa h c)) (Z_to_bv 64 (2^18)) = true ->
      ff_K (h_ugrow h c) (fixrw_commit 0x32 (uaa h c) (2^18) mo);
  ff_u_fresh : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_user (h_reg h c) + kUserMapSize <= kUserLimit -> ff_K h mo ->
      region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 (uaa h c)) (Z_to_bv 64 (2^18)) = true ->
      ff_K (h_ugrow h c) (fixrw_fresh 0x32 (uaa h c) (2^18) mo);
  ff_u_room : forall h c mo, WFK h -> 1 <= c <= 31 -> r_mapped_user (h_reg h c) + kUserMapSize <= kUserLimit -> ff_K h mo ->
      fixrw_grantable 0x32 (uaa h c) (2^18) mo;
  ff_u_scar : forall h c, WFK h -> 1 <= c <= 31 -> r_mapped_user (h_reg h c) + kUserMapSize <= kUserLimit ->
      scar_site AL (ff_CS h) (ff_K h) (uaa h c) (2^18);
  (* [comment removed for export] *)
  ff_madv_ok : forall h k i mo, WFK h -> nth_error (s_chunks (h_sec h)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k))) ->
      shpb (ck_map_beg k) < shpe (ck_map_beg k) (ck_map_size k) -> ff_K h mo ->
      let PB := shpb (ck_map_beg k) in let nZ := shpe (ck_map_beg k) (ck_map_size k) - PB in
      madvise_dontneed_ok (m_vmmaps mo) (Z_to_bv 64 PB) (Z_to_bv 64 nZ) = true;
  ff_madv : forall h k i mo, WFK h -> nth_error (s_chunks (h_sec h)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k))) ->
      shpb (ck_map_beg k) < shpe (ck_map_beg k) (ck_map_size k) -> ff_K h mo ->
      let PB := shpb (ck_map_beg k) in let nZ := shpe (ck_map_beg k) (ck_map_size k) - PB in
      ff_K h (madvise_model PB nZ mo);
  ff_unmap_has : forall h k i mo, WFK h -> nth_error (s_chunks (h_sec h)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k))) ->
      ff_K h mo -> map_has (vm_maps (m_vmmaps mo)) (Z_to_bv 64 (ck_map_beg k)) (Z_to_bv 64 (page_round_up_Z (ck_map_size k))) = true;
  ff_unmap : forall h k i mo, WFK h -> nth_error (s_chunks (h_sec h)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k))) ->
      ff_K h mo -> ff_K (h_rec_sec h k i) (munmap_model (ck_map_beg k) (page_round_up_Z (ck_map_size k)) mo);
  (* [comment removed for export] *)
  ff_node : forall h nb bl mo (a : word), WFK h -> nb = d_nb (h_dep h) /\ bl = d_bl (h_dep h) -> ff_K (hdep h nb bl) mo ->
      bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a -> bv_unsigned a + 2^20 <= ACEIL ->
      region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 (2^20)) = true ->
      ff_K (hdep h (nb ++ [bv_unsigned a]) bl) (anon_grant 0x22 a (2^20) mo) /\ crange (ff_CS (hdep h (nb ++ [bv_unsigned a]) bl)) (bv_unsigned a) (2^20);
  ff_store : forall h nb bl mo (a : word), WFK h -> bl = d_bl (h_dep h) /\ (nb = d_nb (h_dep h) \/ exists x, nb = d_nb (h_dep h) ++ [x]) ->
      ff_K (hdep h nb bl) mo ->
      bv_unsigned a mod 4096 = 0 -> 0 < bv_unsigned a -> bv_unsigned a + 2^23 <= ACEIL ->
      region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) a (Z_to_bv 64 (2^23)) = true ->
      ff_K (hdep h nb (bl ++ [bv_unsigned a])) (anon_grant 0x4022 a (2^23) mo) /\ crange (ff_CS (hdep h nb (bl ++ [bv_unsigned a]))) (bv_unsigned a) (2^23);
  ff_room_n : forall h nb bl mo, WFK h -> nb = d_nb (h_dep h) /\ bl = d_bl (h_dep h) -> ff_K (hdep h nb bl) mo ->
      exists a, anon_grantable 0x22 (2^20) mo a;
  ff_room_s : forall h nb bl mo, WFK h -> bl = d_bl (h_dep h) /\ (nb = d_nb (h_dep h) \/ exists x, nb = d_nb (h_dep h) ++ [x]) ->
      ff_K (hdep h nb bl) mo -> exists a, anon_grantable 0x4022 (2^23) mo a;
  (* [comment removed for export] *)
  ff_cs_mono_fa : forall h c x, ff_CS h x -> ff_CS (h_fagrow h c) x;
  ff_cs_mono_u : forall h c x, ff_CS h x -> ff_CS (h_ugrow h c) x;
  (* [comment removed for export] *)
  ff_cs_rec_sec : forall h k i x, nth_error (s_chunks (h_sec h)) i = Some (SH (ck_map_beg k) (ck_map_size k) (needed2 (ck_n k))) ->
      ff_CS h x -> ~ (ck_map_beg k <= x < ck_map_beg k + ck_map_size k) -> ff_CS (h_rec_sec h k i) x;
  ff_cs_mono_dep : forall h nb bl sn sb x, ff_CS (hdep h nb bl) x -> ff_CS (hdep h (nb ++ sn) (bl ++ sb)) x
}.

(* [comment removed for export] *)

(* [comment removed for export] *)

End ARUN_1.
