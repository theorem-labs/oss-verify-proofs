(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr MState Frame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma amd_frame_io : forall md md', amd_frame md md' -> m_fs md' = m_fs md /\ m_fds md' = m_fds md /\ m_halted md' = None.
Proof.
  (intros md md'; (first [ intro dR_1; dand11 dR_1 as Hfd _ Hfs _ _ _ _ _ _ _ Hh | intros (Hfd & _ & Hfs & _ & _ & _ & _ & _ & _ & _ & Hh) ])). unfold m_fs, m_fds. rewrite Hfd, Hfs. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto.
Qed.


(* [comment removed for export] *)
Section S16.
  Context {Clg : Ceiling} {AI : AsanAlloc LPA} {AI16 : AsanAlloc16}.
  #[local] Notation rom := (seg_rom rsegs).

  Lemma ret_pc_ra4 : forall ra : word, bv_unsigned ra mod 4 = 0 -> ret_pc ra = ra.
  Proof.
    intros ra RA4.
    assert (E2 : bv_unsigned ra mod 2 = 0).
    { clear - RA4. apply Z.mod_divide in RA4; [|lia]. destruct RA4 as [q Hq]. rewrite Hq.
      replace (q * 4) with ((q * 2) * 2) by lia. apply Z.mod_mul. lia. }
    pose proof (bv_unsigned_in_range 64 ra) as R. unfold bv_modulus in R.
    rewrite <- (Z_to_bv_bv_unsigned ra). apply ret_pc_even; [lia | exact E2].
  Qed.

  Definition malloc1_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (n : Z) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = wz n -> 1 <= n < REQ_MAX -> n <= NREQ_CAP ->
      a_livebytes A + n <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (n < 16 -> 1 <= a_tinycred A) ->
      (kMaxPrimaryUser < n -> 1 <= a_seccred A) -> prim_cost n <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites LPA) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (* [comment removed for export] *)
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          hull_le (ahull A) (ahull A') ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          r <> 0 -> a_live A r = None -> a_live A' r = Some n -> (forall q, q <> r -> a_live A' q = a_live A q) ->
          a_livebytes A' = a_livebytes A + n ->
          a_tinycred A' = a_tinycred A - (if Z.ltb n 16 then 1 else 0) -> a_nlive A' = a_nlive A + 1 ->
          a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) ->
          a_primcred A' = a_primcred A - prim_cost n (* [comment removed for export] *) ->
          frame_ok LPA (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (newblk r n) v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' rom) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_malloc_pc LPA) fc None m rom) md) T.

  Theorem malloc1_ok : malloc1_stmt.
  Proof.
    unfold malloc1_stmt. intros until T. cbv zeta.
    intros AINV MI A0 N1 NC LB NL TC SC PCC TP SPA RA4 SITE S0C CEIL SM KK.   (* [comment removed for export] *)
    rewrite (ret_pc_ra4 ra RA4) in KK.
    pose proof (as_malloc_cps16 (AsanAlloc16:=AI16)) as MA. unfold as_malloc_cps16_stmt in MA. cbv zeta in MA.
    eapply (MA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A n T
               AINV MI A0 N1 NC LB NL TC SC PCC TP SPA RA4 SITE S0C CEIL SM).
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AINV' MI' FR HLE FF TC' (RNZ & LVA & LV' & LVO & LB' & NL' & SC' & PC') FOK.   (* [comment removed for export] *)
    exact (KK t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' r A' m' md' AINV' MI' FR HLE FF RNZ LVA LV' LVO LB' TC' NL' SC' PC' FOK).
  Qed.

  Definition free1_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (p n0 : Z) (T : TSet),
      let v := aview A m in
      ainv A m md -> mem_inv rsegs v ->
      a0 = wz p -> ((p = 0 /\ n0 = 0) \/ a_live A p = Some n0) ->
      tp = cl_tp LPA -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites LPA) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview A' m' in
          ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md md' ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_live A' p = None -> (forall q, q <> p -> a_live A' q = a_live A q) ->
          a_livebytes A' = a_livebytes A - n0 -> a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A - (if Z.eqb p 0 then 0 else 1) ->
          a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A (* [comment removed for export] *) ->
          frame_ok LPA (owned A) (owned A') (bv_unsigned sp) ASTK (newblk p n0) nowhere v v' ->
          srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' rom) md') T) ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_free_pc LPA) fc None m rom) md) T.

  Theorem free1_ok : free1_stmt.
  Proof.
    unfold free1_stmt. intros until T. cbv zeta.
    intros AINV MI A0 LV TP SPA RA4 SITE S0C CEIL SM KK.
    rewrite (ret_pc_ra4 ra RA4) in KK.
    eapply (as_free_cps LPA ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m md A p n0 T
              AINV MI A0 LV TP SPA RA4 SITE S0C CEIL SM).
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md'. cbv zeta.
    intros AINV' MI' FR _ FF L0 LQ LB TC SC PC NL _ FOK.   (* [comment removed for export] *)
    exact (KK t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A' m' md' AINV' MI' FR FF L0 LQ LB TC NL SC PC FOK).
  Qed.
End S16.
