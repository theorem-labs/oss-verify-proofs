(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import CellsX X509Aux HeapIface Asn1Aux Frame.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepFacts RepName RepCrt CrtFacts CrtStmts SInv SInvFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_pkcs7_getcerts.     (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_alloc_lib A_mpi_read_binary_stmt A_asn1_get_tag_stmt A_asn1_get_tag A_asn1_get_int
     A_asn1_get_alg_null_A A_oid A_pkcs7_nextlen A_pkcs7_cinfo A_crt_stmts A_crt_parse_stmts A_pkcs7_getcerts_stmtC A_pkcs7_top A_fuzz_entry A_pkcs7_free A_pkcs7_getcerts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_pkcs7_top24 A_pkcs7_getcerts_stmt24 A_pkcs7_parse_A A_pkcs7_parse_C.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import AUnw. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_x509_crt_free A_pkcs7_parse_A24 A_pkcs7_parse_B24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import A_frame_lib A_frame_kit.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.



(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Lemma cnt24_all_small : forall l : list blk, List.Forall (fun b => snd b < 5889) l -> cnt24 l = 0.
Proof.
  induction l as [|b l IH]; intros FA; [apply cnt24_nil|]. inversion FA as [|b' l' Hb Hl]; subst. destruct b as [B k]. cbn [snd] in Hb.
  etransitivity; [exact (cnt24_cons_small B k l Hb)| apply IH; exact Hl].
Qed.
Lemma sname_small : forall l, List.Forall (fun b : blk => snd b < 5889) (SNAME l).
Proof. intros l. unfold SNAME. apply List.Forall_forall. intros b Hb. apply in_map_iff in Hb. ddestruct Hb as (a & <- & _). cbn [snd]. unfold NAME_SIZE. lia. Qed.
Lemma signer_blocks_small : forall l, List.Forall (fun b : blk => snd b < 5889) (signer_blocks l).
Proof.
  induction l as [|e r IH]; cbn [signer_blocks]; [constructor|].
  apply List.Forall_app. split; [| exact IH]. apply List.Forall_app. split; [exact (sname_small (snd e))|].
  constructor; [cbn [snd]; unfold SIGNER_SIZE; lia| constructor].
Qed.
Lemma cnt24_signers : forall LBs names sg, Permutation LBs (SNAME names ++ signer_blocks sg) -> cnt24 LBs = 0.
Proof.
  intros LBs names sg PM. apply cnt24_all_small. eapply Permutation_Forall; [apply Permutation_sym; exact PM|].
  apply List.Forall_app. split; [apply sname_small| apply signer_blocks_small].
Qed.
(* [comment removed for export] *)
Ltac blk_norm_goal := change (@cons (Z * Z)%type) with (@cons blk); change (@app (Z * Z)%type) with (@app blk); change (@nil (Z * Z)%type) with (@nil blk).
Ltac blk_norm_in H := change (@cons (Z * Z)%type) with (@cons blk) in H; change (@app (Z * Z)%type) with (@app blk) in H; change (@nil (Z * Z)%type) with (@nil blk) in H.
(* [comment removed for export] *)
Ltac c24_dva Hn :=
  lazymatch goal with |- cnt24 _ <= cnt24 _ + 1 + 2 * (_ / 5889) => idtac end;
  cbn [app]; blk_norm_goal;
  let DP := fresh "DP" in
  match goal with |- _ <= _ + 1 + 2 * (?q / 5889) => pose proof (Z.div_pos q 5889 ltac:(clear - Hn; lia) ltac:(clear; lia)) as DP end;
  first [ (clear - DP; lia)
        | match goal with |- cnt24 (?b :: ?l) <= _ => let CC := fresh "CC" in pose proof (cnt24_cons_le b l) as CC; clear - DP CC; lia end ].


Section Walk.
  Variable R : art_layout.
  #[local] Hint Extern 0 heap_layout => exact (arl_L R) : typeclass_instances.
  Variable HIA : artA asegs R.
  Local Notation AL := (arl_AL R).
  Local Notation L := (arl_L R).
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis UARG : arl_uar_got R = A_UAR_GOT.
  Hypothesis SM2 : arl_smalloc R 2 = A_SMALLOC_2.
  Hypothesis NS1 : 0 <= arl_need_smalloc R.
  Hypothesis DIMG : hl_img_lo L <= hl_data_lo L /\ hl_data_hi L <= hl_img_hi L.
  Hypothesis HMND : forall h LB LF m, HM asegs R HIA h LB LF m -> List.NoDup (map fst LB).
  Variable PK : pk_class asegs.
  Variable SI : sinv (arl_L R).
  (* [comment removed for export] *)
  Hypothesis GETTAG : asn1_get_tag_stmtA asegs AL A_ASN1_GET_TAG_G.
  (* [comment removed for export] *)
  Variables (PHIg : Z -> Z) (FFRg : Z -> Z -> Z) (CNTg : Z -> Z) (STKg : Z).
  Variable C24c : Z.   (* [comment removed for export] *)
  Hypothesis C24c0 : 0 <= C24c.
  Hypothesis GETCERTS : pkcs7_get_certs_stmtA24 asegs R HIA PK SI PHIg FFRg CNTg STKg C24c A_PKCS7_GETCERTS.
  Variables (PHIs : Z -> Z) (FFRs : Z -> Z -> Z) (CNTs : Z -> Z) (STKs : Z).
  Hypothesis GETSIGNERS : pkcs7_getsigners_stmtA asegs R HIA PHIs FFRs CNTs STKs A_PKCS7_GETSIGNERS.
  (* [comment removed for export] *)
  Variables (PHIj : Z -> Z) (FFRj : Z -> Z -> Z) (CNTj : Z -> Z).
  Variables (PHIf : Z -> Z) (FFRf : Z -> Z -> Z) (STKf : Z).
  Hypothesis PKFREE : pkcs7_free_stmtA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) PHIf FFRf STKf A_PKCS7_FREE.
  Hypothesis PHIg_mono : forall n n', 0 <= n <= n' -> 0 <= PHIg n <= PHIg n'.
  Hypothesis FFRg_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRg n d <= FFRg n' d.
  Hypothesis CNTg_mono : forall n n', 0 <= n <= n' -> 0 <= CNTg n <= CNTg n'.
  Hypothesis PHIs_mono : forall n n', 0 <= n <= n' -> 0 <= PHIs n <= PHIs n'.
  Hypothesis FFRs_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRs n d <= FFRs n' d.
  Hypothesis CNTs_mono : forall n n', 0 <= n <= n' -> 0 <= CNTs n <= CNTs n'.
  Hypothesis PHIj_mono : forall n n', 0 <= n <= n' -> 0 <= PHIj n <= PHIj n'.
  Hypothesis FFRj_mono : forall n n' d, 0 <= n <= n' -> 0 <= FFRj n d <= FFRj n' d.
  Hypothesis CNTj_mono : forall n n', 0 <= n <= n' -> 0 <= CNTj n <= CNTj n'.
  Hypothesis PHIj_joint : forall a b, 0 <= a -> 0 <= b -> PHIg a + PHIs b <= PHIj (a + b).
  Hypothesis FFRj_joint : forall a b d, 0 <= a -> 0 <= b -> FFRg a d + FFRs b d <= FFRj (a + b) d.
  Hypothesis CNTj_joint : forall a b, 0 <= a -> 0 <= b -> CNTg a + CNTs b <= CNTj (a + b).
  Hypothesis PHIf_mono : forall k k', 0 <= k <= k' -> 0 <= PHIf k <= PHIf k'.
  Hypothesis FFRf_mono : forall k k' d, 0 <= k <= k' -> 0 <= FFRf k d <= FFRf k' d.
  Hypothesis STKg0 : 0 <= STKg. Hypothesis STKs0 : 0 <= STKs. Hypothesis STKf0 : 0 <= STKf.
  (* [comment removed for export] *)
  Local Notation STKp := (STKp R STKg STKs STKf).

  (* [comment removed for export] *)
  #[using="PHIj_mono FFRj_mono CNTj_mono"] Lemma joint_0 : forall n, 0 <= n -> 0 <= PHIj n /\ (forall dd, 0 <= FFRj n dd) /\ 0 <= CNTj n.
  Proof.
    intros n0 Hn0. pose proof (PHIj_mono 0 n0 ltac:(clear - Hn0; lia)) as X1. pose proof (CNTj_mono 0 n0 ltac:(clear - Hn0; lia)) as X3.
    split; [clear - X1; lia|]. split; [intros dd; pose proof (FFRj_mono 0 n0 dd ltac:(clear - Hn0; lia)) as X2; clear - X2; lia| clear - X3; lia].
  Qed.
  #[using="PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint"] Lemma joint_gs : forall c s n, 0 <= c -> 0 <= s -> c + s <= n ->
    PHIg c + PHIs s <= PHIj n /\ (forall dd, FFRg c dd + FFRs s dd <= FFRj n dd) /\ CNTg c + CNTs s <= CNTj n.
  Proof.
    intros c s0 n0 Hc Hs Hcs.
    pose proof (PHIj_joint c s0 Hc Hs) as J1. pose proof (CNTj_joint c s0 Hc Hs) as J3.
    pose proof (PHIj_mono (c + s0) n0 ltac:(clear - Hc Hs Hcs; lia)) as M1. pose proof (CNTj_mono (c + s0) n0 ltac:(clear - Hc Hs Hcs; lia)) as M3.
    split; [clear - J1 M1; lia|]. split; [| clear - J3 M3; lia].
    intros dd. pose proof (FFRj_joint c s0 dd Hc Hs) as J2. pose proof (FFRj_mono (c + s0) n0 dd ltac:(clear - Hc Hs Hcs; lia)) as M2. clear - J2 M2. lia.
  Qed.
  #[using="PHIs FFRs CNTs PHIs_mono FFRs_mono CNTs_mono PHIj_mono FFRj_mono CNTj_mono PHIj_joint FFRj_joint CNTj_joint"] Lemma joint_g : forall c n, 0 <= c <= n -> PHIg c <= PHIj n /\ (forall dd, FFRg c dd <= FFRj n dd) /\ CNTg c <= CNTj n.
  Proof.
    intros c n0 Hc. ddestruct (joint_gs c 0 n0 ltac:(clear - Hc; lia) ltac:(clear; lia) ltac:(clear - Hc; lia)) as (J1 & J2 & J3).
    pose proof (PHIs_mono 0 0 ltac:(clear; lia)) as S1. pose proof (CNTs_mono 0 0 ltac:(clear; lia)) as S3.
    split; [clear - J1 S1; lia|]. split; [| clear - J3 S3; lia].
    intros dd. specialize (J2 dd). pose proof (FFRs_mono 0 0 dd ltac:(clear; lia)) as S2. clear - J2 S2. lia.
  Qed.
  
  Section Call.
  Variables (h : HST asegs R HIA) (LB LF : list blk).
  Local Notation CS := (hcs asegs R HIA h).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo0 : Model)
            (A DATA n lo slo d : Z) (bs : list byte).
  Hypothesis P7Z : pkcs7_zero asegs m A.
  Hypothesis AAL : A mod 8 = 0.
  Hypothesis A0 : 0 < A.
  Hypothesis CWA : client_wrange L (LB ++ fdata LF) lo (htop asegs R HIA h) A PKCS7_SIZE.
  Hypothesis ASTK : A + PKCS7_SIZE <= arl_stklo R.
  Hypothesis AOD : A + PKCS7_SIZE <= hl_data_lo L \/ hl_data_hi L <= A.
  Hypothesis HBY : bytes_at asegs m DATA bs.
  Hypothesis LEN : Z.of_nat (length bs) = n.
  Hypothesis Hn : 0 <= n < 2 ^ 26.
  Hypothesis HD : 0 < DATA.
  Hypothesis CRD : client_range L (LB ++ fdata LF) lo DATA n.
  Hypothesis DLO : DATA + n <= lo \/ bv_unsigned sp <= DATA.
  Hypothesis DA : n = 0 \/ A + PKCS7_SIZE <= DATA \/ DATA + n <= A.
  Hypothesis SLOS : arl_stklo R <= slo.
  Hypothesis SLOL : slo <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - STKp.
  Hypothesis TOP : bv_unsigned sp <= htop asegs R HIA h.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis SPH : bv_unsigned sp <= 2^47.
  Hypothesis TPV : tp = Z_to_bv 64 (arl_tp R).
  Hypothesis LFB : (length LF <= 33)%nat.
  Hypothesis C24H : cnt24 LB + 1 + 2 * (n / 5889) + C24c <= C24MAX.     (* [comment removed for export] *)
  Let LOS : arl_stklo R <= lo := Z.le_trans _ _ _ SLOS SLOL.
  Let ALO1 : A + PKCS7_SIZE <= lo. Proof. pose proof LOS. pose proof ASTK. lia. Qed.

  Ltac rt_facts :=
    pose proof (hcs_ok asegs R HIA h) as CSOK;
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof (art_alwf asegs R HIA) as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG';
    pose proof (art_uar_img asegs R HIA) as UIMG;
    pose proof (art_lo asegs R HIA) as ALO;
    pose proof (alloc_ceiling_pos (L := arl_L R)) as ACP; pose proof (alloc_ceiling_val R) as ACV;
    unfold A_UAR_GOT in UARG; unfold A_SMALLOC_2 in SM2; unfold A_pkcs7_parse_A.STKp in SLO; unfold PKCS7_SIZE in *;
    pose proof (hcs_stack asegs R HIA h) as SCS0;
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn [Z.pow Z.of_N Pos.pow] in SPR.

  (* [comment removed for export] *)
  Local Notation FSHXL :=
    [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242);
     C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
  Local Notation SAVEL := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].



  (* [comment removed for export] *)
  Local Notation CNTp := (A_pkcs7_parse_C.CNTp CNTj).
  Local Notation PHIp := (A_pkcs7_parse_C.PHIp PHIj CNTj PHIf).
  Local Notation FFRp := (A_pkcs7_parse_C.FFRp FFRj CNTj FFRf).

  Local Notation POST := (pkcs7_parse_der_postA24 asegs R HIA (option (p7_own * p7_junk)) (p7repA PK) SI PHIp FFRp CNTp
                            h LB LF ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n lo slo d m mo0).
  Local Notation X0 := [(A, A + 1440)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition dvA (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 : word) (g4 g8 g12 g16 g18 g22 : list byte) (fsh : list cell)
      (v16 v24 : word) (j32 : list byte) (v48 : word) (alg : list byte) (v80 : word) (cs : list cell)
      (Lc : list blk) (mc : mem) (moc : Model) (hc : HST asegs R HIA) : Prop :=
    HM asegs R HIA hc (Lc ++ LB) ((FB, 256) :: LF) mc /\ HK asegs R HIA hc moc /\ mo_frame mo0 moc
    /\ htop asegs R HIA hc = htop asegs R HIA h /\ hstkhi asegs R HIA hc = hstkhi asegs R HIA h /\ hflag asegs R HIA hc = hflag asegs R HIA h
    /\ (forall x, CS x -> hcs asegs R HIA hc x)
    /\ havol asegs R HIA hc <= havol asegs R HIA h + PHIa /\ hfr asegs R HIA hc <= hfr asegs R HIA h + FFRa
    /\ presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m mc /\ si_P SI mc
    /\ bv_unsigned sp - 208 <= sp1 <= bv_unsigned sp - 192 /\ sp1 mod 32 = 0 /\ FB mod 64 = 0 /\ fresh_apart R LB LF FB 256
    /\ crange CS FB 256
    /\ rw_cells asegs mc FB [C8 w0; C8 w1; C8 w2]
    /\ rw_cells asegs mc (FB + 32) [CB 8 g4] /\ rw_cells asegs mc (FB + 64) [CB 8 g8] /\ rw_cells asegs mc (FB + 96) [CB 8 g12]
    /\ rw_cells asegs mc (FB + 128) [CB 8 g16] /\ rw_cells asegs mc (FB + 144) [CB 8 g18] /\ rw_cells asegs mc (FB + 176) [CB 8 g22]
    /\ rw_cells asegs mc (Z.shiftr FB 3 + al_sb AL) fsh
    /\ rw_cells asegs mc (bv_unsigned sp + -104) SAVEL
    /\ rw_cells asegs mc (sp1 + 16) [C8 v16; C8 v24; CB 16 j32; C8 v48; CB 24 alg; C8 v80]
    /\ stk asegs mc sp1 (sp1 + 16) /\ stk asegs mc (sp1 + 88) (bv_unsigned sp + -104) /\ stk asegs mc lo sp1
    /\ rw_cells asegs mc A cs /\ cells_size cs = 1440%nat /\ aobj asegs AL CS mc A 1440
    /\ mem_inv asegs mc /\ sshad asegs AL mc slo (bv_unsigned sp)
    /\ cnt24 (Lc ++ LB) <= cnt24 LB + 1 + 2 * (n / 5889).

  Ltac dvA_open D :=
    destruct D as (HHc & HKc & MFc & HTc & HSc & HFc & HCSc & HVc & HFRc & PRES & SIc & SP1 & SP1M & F64 & FRSH & CFB
                   & FHD & G4 & G8 & G12 & G16 & G18 & G22 & FSH & SAVE & RSL
                   & STa & STb & STlo & CELLS & SZC & OBJA & MIc & SSc & C24i).

  (* [comment removed for export] *)
  #[using="h sp n lo slo bs A0 CWA ASTK LEN Hn SLOS SLOL LFB LOS ALO1"] Lemma pkcs7_at_presx0 : forall st mc m' Lc hq SPq LFq,
    pkcs7_at asegs PK st mc Lc LB A -> HM asegs R HIA hq (Lc ++ LB) LFq mc ->
    heap_presx asegs L ((Lc ++ LB) ++ fdata LF) SPq [] mc m' -> mem_inv asegs m' ->
    pkcs7_at asegs PK st m' Lc LB A.
  Proof.
    intros st mc m' Lc hq SPq LFq REP HH HPX MI'.
    pose proof (alloc_ceiling_val R) as ACV. pose proof ALO1 as ALO1'. unfold PKCS7_SIZE in ALO1'.
    assert (HPX' : heap_presx asegs L (Lc ++ LB) SPq [] mc m').
    { eapply heap_presx_weaken; [exact HPX| intros b Hb; apply in_app_iff; left; exact Hb| apply Z.le_refl| intros x Hx; exact Hx]. }
    assert (BB : blocks_below (Lc ++ LB) alloc_ceiling) by (eapply (blocks_below_hm R HIA); [exact HH| intros b Hb; exact Hb]).
    assert (CRAq : client_range L ((Lc ++ LB) ++ fdata LF) SPq A 1440).
    { eapply client_range_lower; [| exact ALO1']. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWA)|].
      intros b Hb. apply in_app_iff in Hb. apply in_app_iff. destruct Hb as [Hb|Hb]; [left; apply in_app_iff; right; exact Hb| right; exact Hb]. }
    destruct st as [[po pj]|].
    - ddestruct REP as (LIVE & NDn & IFF).
      ddestruct LIVE as (HC & HAL & HA & AB & RP & RL & RIN & RC & OWN & HN & HS & NDp).
      split; [| exact (conj NDn IFF)].
      assert (INp : forall b, In b (p7_blocks po) -> In b (Lc ++ LB)) by (intros b Hb; apply in_app_iff; left; apply (proj2 (IFF b)); exact Hb).
      refine (conj _ (conj HAL (conj HA (conj AB (conj RP (conj RL (conj RIN (conj _ (conj _ (conj _ (conj _ NDp))))))))))).
      + eapply heap_presx_rw_cells; [exact HPX| exact HC| | exact I]. change (Z.of_nat (cells_size (pkcs7_cells po pj))) with 1440. exact CRAq.
      + destruct (Z.eq_dec (po_rawlen po) 0) as [L0|L0].
        * rewrite L0 in RC |- *. change (Z.to_nat 0) with 0%nat in RC |- *. eapply rw_cells_CB0. exact RC.
        * eapply heap_presx_rw_cells; [exact HPX'| exact RC| | exact I].
          cbn [cells_size csize Nat.add]. rewrite Nat.add_0_r, Z2Nat.id by lia. eapply client_range_block; [exact RIN| lia| lia].
      + eapply (crt_own_ok_presx asegs L PK) with (CE := alloc_ceiling) (X := []); [exact OWN| | exact HPX'| exact BB| constructor| clear - ACV; lia| exact MI'].
        intros b Hb. apply INp. unfold p7_blocks. apply in_app_iff; right. apply in_app_iff; left. exact Hb.
      + eapply (chain_presx' asegs L) with (CE := alloc_ceiling) (X := []); [exact HN| | exact HPX'| unfold NAME_SIZE; lia| exact BB| constructor].
        intros x Hx. apply INp. unfold p7_blocks. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; left. apply (in_map (fun a => (a, NAME_SIZE))). exact Hx.
      + eapply (signer_chain_presx' asegs L) with (CE := alloc_ceiling) (X := []); [exact HS| | exact HPX'| exact BB| constructor].
        intros b Hb. apply INp. unfold p7_blocks. apply in_app_iff; right. apply in_app_iff; right. apply in_app_iff; right. exact Hb.
    - ddestruct REP as (PZ & HAL & HA & AB). split; [| exact (conj HAL (conj HA AB))].
      eapply heap_presx_rw_cells; [exact HPX| exact PZ| exact CRAq| exact I].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf STKg0 bs A0 CWA ASTK LEN Hn SLOS SLOL SLO TOP SPH LFB LOS ALO1"] Lemma ret_walk : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 : word) (g4 g8 g12 g16 g18 g22 : list byte)
      (v16 v24 : word) (j32 : list byte) (v48 : word) (alg : list byte) (v80 : word) (cs : list cell)
      (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : byte)
      Lc mc moc hc (st : option (p7_own * p7_junk)) (r : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s5v s6v s8v s9v : word),
    dvA FB sp1 W PHIa FFRa w0 w1 w2 g4 g8 g12 g16 g18 g22
        [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15;
         C1 b16; C1 b17; C1 b18; C1 b19; C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31]
        v16 v24 j32 v48 alg v80 cs Lc mc moc hc ->
    pkcs7_at asegs PK st mc Lc LB A -> p7small st ->
    Z.of_nat (length Lc) <= CNTp n -> PHIa <= PHIp n -> FFRa <= FFRp n d ->
    (forall x, outside (X0 ++ si_fp SI) x -> outside W x) ->
    -2^31 <= r < 2^31 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      s2v (Z_to_bv 64 (-8)) (Z_to_bv 64 r) s5v s6v (Z_to_bv 64 FB) s8v s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97ae8) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D REP SM CNT PHI FFR HW Hr. dvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKg0 STKs0 STKf0 TOP HT; lia]).
    pose proof (fresh_apart_grow R HIA hc Lc LB LF mc FB 256 FRSH HHc) as FRSH3.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lc ++ LB) LF mc FB 256 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (_ & INF & INH & IND & AP & _ & F8 & FBLO & _ & _).
    pose proof (frame_apart_obj R HIA LB LF lo _ A 1440 FB 256 FRSH CWA ltac:(clear; lia) ltac:(clear; lia) LOS) as APPA.
    pose proof OBJA as CRA. apply aobj_crange in CRA.
    (* [comment removed for export] *)
    chunk_to_stk RSL.
    stk_merge_into STa RSL. stk_merge_into STa STb.
    pose proof (conj CELLS I) as CELLw. apply rw_cells_blob in CELLS. rewrite SZC in CELLS.
    pose proof (presW_hmono R HIA h hc LB LF _ _ _ m mc PRES HCSc HSc) as PRESh.
    pose proof (presW_init_at R HIA hc _ _ (Lc ++ LB) LF mc (bv_unsigned sp) (bv_unsigned sp) [] h HHc
                  ltac:(intros b Hb; exact Hb) ltac:(intros fb Hfb; right; exact Hfb) HCSc HSc ltac:(clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia)) as PRES2.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    eapply (aevtA_cut_evtA_KF asegs R HIA hc moc).
    { eapply epi_walk with (h := h) (A := A) (n := n) (lo := lo) (slo := slo) (bs := bs) (STKg := STKg) (STKs := STKs) (STKf := STKf)
                           (h3 := hc) (LBn := Lc) (m0 := m) (m2x := mc) (WA := W) (WB := []);
        first [ exact HHc | exact HCSc | exact PRESh | exact PRES2 | exact CELLS | exact CRA | exact CFB | exact APPA | exact Hr
              | lazymatch goal with |- lo <= bv_unsigned sp - A_pkcs7_parse_A.STKp _ _ _ _ => unfold A_pkcs7_parse_A.STKp; exact SLO end
              | eassumption | reflexivity
              | match goal with |- ?g => idtac "RET-EPI-PRE-LEFT:" g end ]. }
    cbv beta. intros ms9 EP.
    ddestruct EP as (m9 & h4 & z0 & z1 & z2 & za0 & za1 & za2 & za3 & za4 & za5 & za6 & za7 & z3 & z4 & z5 & z6
                    & -> & Ea0 & MI9 & ST9 & SS9 & PRES9 & PRES29 & E4cs & E4top & E4stk & E4flag & E4vol & E4fr & HKI4 & HH4 & HA9).
    apply aevtA_done. intros mo9 [HK9 MF9].
    unfold pkcs7_parse_der_postA24, PKCS7_SIZE.
    deexists 15. dexists m9, mo9, h4, st, Lc.
    split; [reflexivity|].
    split; [exact MI9|]. split; [exact ST9|]. split; [exact SS9|]. split; [eapply mo_frame_trans; [exact MFc| exact MF9]|].
    split.
    { pose proof (presW_presA asegs R HIA hc LB LF _ _ _ _ _ PRES9) as HPF. rewrite HSc in HPF.
      eapply presA_weaken; [exact HPF| intros b Hb; exact Hb| intros b Hb; exact Hb| clear; lia| clear; lia| clear; lia| exact HW]. }
    split; [rewrite E4top; exact HTc|]. split; [rewrite E4stk; exact HSc|]. split; [rewrite E4flag; exact HFc|].
    split; [apply (proj2 (HKI4 mo9)); exact HK9|].
    split; [intros x Hx; rewrite E4cs; exact (HCSc x Hx)|].
    split; [rewrite E4vol; clear - HVc PHI; lia|].
    split; [rewrite E4fr; clear - HFRc FFR; lia|].
    split; [exact CNT|].
    split.
    { split; [| exact SM]. eapply (pkcs7_at_presx0 st mc m9 Lc hc); [exact REP| exact HHc| | exact MI9].
      exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29)). }
    split; [exact HH4|].
    split; [eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ (presW_presA asegs R HIA hc _ LF _ _ _ _ _ PRES29))| intros a _; exact I]|].
    exact C24i.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="IMG NS1 STKg STKs STKf PKFREE PHIf_mono FFRf_mono STKg0 bs AAL A0 CWA ASTK AOD LEN Hn SLOS SLOL SLO TOP SPH TPV LFB LOS ALO1"] Lemma out_walk : forall (FB sp1 : Z) (W : list ivl) (PHIa FFRa : Z) (w0 w1 w2 : word) (g4 g8 g12 g16 g18 g22 : list byte)
      (v16 v24 : word) (j32 : list byte) (v48 : word) (alg : list byte) (v80 : word) (cs : list cell)
      (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 : byte)
      Lc mc moc hc (st : option (p7_own * p7_junk)) (r : Z)
      (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s2v s5v s6v s9v : word),
    dvA FB sp1 W PHIa FFRa w0 w1 w2 g4 g8 g12 g16 g18 g22
        [C1 b0; C1 b1; C1 b2; C1 b3; C1 b4; C1 b5; C1 b6; C1 b7; C1 b8; C1 b9; C1 b10; C1 b11; C1 b12; C1 b13; C1 b14; C1 b15;
         C1 b16; C1 b17; C1 b18; C1 b19; C1 b20; C1 b21; C1 b22; C1 b23; C1 b24; C1 b25; C1 b26; C1 b27; C1 b28; C1 b29; C1 b30; C1 b31]
        v16 v24 j32 v48 alg v80 cs Lc mc moc hc ->
    pkcs7_at asegs PK st mc Lc LB A -> p7small st ->
    Z.of_nat (length Lc) <= CNTp n ->
    PHIa + PHIf (Z.of_nat (length Lc)) <= PHIp n -> FFRa + FFRf (Z.of_nat (length Lc)) 0 <= FFRp n d ->
    (forall x, outside (X0 ++ si_fp SI) x -> outside W x) -> (forall x, outside W x -> outside X0 x) ->
    havol asegs R HIA h + PHIp n <= AVOL_MAX -> hfr asegs R HIA h + FFRp n d <= FR_MAX ->
    -2^31 <= r < 2^31 ->
    aevtS asegs POST
      (mkCfg (MS (mkR xra (Z_to_bv 64 sp1) gp tp t0 t1 t2 sp (Z_to_bv 64 sp1) a0 a1 a2 a3 a4 a5 a6 a7
                      s2v (Z_to_bv 64 (-8)) (Z_to_bv 64 r) s5v s6v (Z_to_bv 64 FB) (Z_to_bv 64 A) s9v
                      (Z_to_bv 64 (Z.shiftr FB 3 + al_sb AL)) (Z_to_bv 64 FB) t3 t4 t5 t6)
                 F (Z_to_bv 64 0x97ae0) fc None mc (seg_rom asegs)) moc).
  Proof.
    intros until s9v. intros D REP SM CNT PHI FFR HW HWX BUD BUDF Hr. pose proof D as D0. dvA_open D. rt_facts.
    pose proof (hm_top asegs R HIA hc _ _ _ HHc) as HT. rewrite HTc, HSc in HT.
    assert (SP1R : 0 <= sp1 < 2^64) by (clear - SP1 SPR SLO LOS ALO ACV NS1 STKg0 STKs0 STKf0; lia).
    assert (SCS : crange CS lo (bv_unsigned sp - lo)) by (eapply crange_sub; [exact SCS0| clear - LOS; lia| clear - SLO NS1 STKg0 STKs0 STKf0 TOP HT; lia]).
    assert (SCSc : crange (hcs asegs R HIA hc) lo (bv_unsigned sp - lo)) by (eapply crange_mono; [exact HCSc| exact SCS]).
    pose proof (fresh_apart_grow R HIA hc Lc LB LF mc FB 256 FRSH HHc) as FRSH3.
    ddestruct (frame_factsA R HIA (hcs asegs R HIA hc) hc (Lc ++ LB) LF mc FB 256 lo HHc eq_refl FRSH3 F64 ltac:(clear; lia) ltac:(reflexivity) LOS)
      as (CFBc & INF & INH & IND & AP & _ & F8 & FBLO & _ & _).
    pose proof FRSH as FRSH'. unfold fresh_apart in FRSH'. ddestruct FRSH' as (F0 & F1 & F2 & F3).
    pose proof (frame_apart_obj R HIA LB LF lo _ A 1440 FB 256 FRSH CWA ltac:(clear; lia) ltac:(clear; lia) LOS) as APPA.
    pose proof (aobj_cs_mono asegs AL _ _ _ _ _ HCSc OBJA) as OBJc.
    assert (CWc : client_wrange L (LB ++ fdata ((FB, 256) :: LF)) lo (htop asegs R HIA hc) A 1440).
    { rewrite HTc. eapply client_wrange_mono; [exact CWA| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    pose proof (PHIf_mono 0 (Z.of_nat (length Lc)) ltac:(clear; lia)) as PF0.
    pose proof (FFRf_mono 0 (Z.of_nat (length Lc)) 0 ltac:(clear; lia)) as FF0.
    apply (aevtA_enter asegs (KF asegs R HIA hc moc) _ _ _ (conj HKc (mo_frame_refl moc))).
    pose proof (AIh_laws asegs R HIA hc) as LAWS. pose proof (KF_kinv asegs R HIA hc moc) as KINV.
    (* [comment removed for export] *)
    zstep. zstep.
    eapply aevtA_call.
    { intros mo1 [HK1 MF1].
      eapply PKFREE with (h := hc) (LB := LB) (LBn := Lc) (LF := (FB, 256) :: LF) (A := A) (lo := lo) (d := 0) (st := st);
        rewrite ?(unsigned_lit sp1) by exact SP1R; unfold PKCS7_SIZE;
        first [ exact HHc | exact HK1 | exact (conj REP SM) | exact AAL | exact A0 | exact OBJc | exact CWc | exact STlo | exact LOS | exact MIc | exact TPV | reflexivity
              | lazymatch goal with
                | |- A + _ <= lo \/ _ => left; clear - ALO1; unfold P_pkcs7_top.PKCS7_SIZE, RepCrt.PKCS7_SIZE in *; lia
                | |- lo <= sp1 - STKf => clear - SLO SP1 NS1 STKg0 STKs0 STKf0; lia
                | |- sp1 <= htop _ _ _ _ => rewrite ?HTc; clear - SP1 TOP; lia
                | |- sp1 mod 16 = 0 => clear - SP1M; Z.div_mod_to_equations; lia
                | |- sp1 <= 2 ^ 47 => clear - SP1 SPH; lia
                | |- havol _ _ _ _ + _ <= AVOL_MAX => clear - HVc PHI BUD PF0; lia
                | |- uw_obj R A _ 0 => left; split; [exact ASTK| clear; lia]
                | |- hfr _ _ _ _ + _ <= FR_MAX => clear - HFRc FFR BUDF FF0; lia
                end
              | match goal with |- ?g => idtac "PKFREE-PRE-LEFT:" g end ]. }
    cbv beta. (intros ms4 mo4 dd_H; ddestruct dd_H as (mo1 & [HK1 MF1] & PO)).
    ddestruct PO as (q0 & q1 & q2 & qa0 & qa1 & qa2 & qa3 & qa4 & qa5 & qa6 & qa7 & q3 & q4 & q5 & q6 & m4 & mo4' & h4 & LBx
                    & E4 & MI4 & ST4 & MF4 & HP4 & HT4 & HS4 & HF4 & HK4 & HCS4 & HV4 & HFR4 & PZ4 & LEN4 & HH4 & C24f).
    injection E4 as Ems Emo. subst ms4 mo4.
    replace (ret_pc (Z_to_bv 64 0x97ae8)) with (Z_to_bv 64 0x97ae8 : word) by (symmetry; apply ret_pc_even; [clear; lia| reflexivity]).
    rewrite (unsigned_lit sp1) in ST4, HP4 by exact SP1R. unfold PKCS7_SIZE in HP4.
    rewrite HTc in HT4. rewrite HSc in HS4, HP4. rewrite HFc in HF4.
    assert (HCSh4 : forall x, CS x -> hcs asegs R HIA h4 x) by (intros x Hx; apply HCS4, HCSc, Hx).
    (* [comment removed for export] *)
    assert (HP4' : presA asegs R LB LF sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4).
    { eapply presA_weaken; [exact HP4| intros b Hb; exact Hb| intros b Hb; right; exact Hb| clear; lia| clear; lia| clear; lia| intros x Hx; exact Hx]. }
    assert (PRES' : presW asegs R HIA h LB LF (bv_unsigned sp) (bv_unsigned sp) W m m4).
    { ddestruct PRES as (P0 & C1 & C2 & C3). split; [| split; [exact C1| split; [exact C2| exact C3]]].
      eapply presA_trans; [exact P0|].
      eapply presA_weaken; [exact HP4'| intros b Hb; exact Hb| intros b Hb; exact Hb| clear - SP1; lia| clear - LOS SLO NS1 STKg0 STKs0 STKf0; lia| clear; lia| exact HWX]. }
    assert (CSHD : forall LBq SSPq TOPq c, FB <= c < FB + 256 -> cshd R LBq ((FB, 256) :: LF) SSPq TOPq c).
    { intros LBq SSPq TOPq c Hc. right; right; left. exists (FB, 256). split; [left; reflexivity| cbn; exact Hc]. }
    assert (DJ : forall Aq k, FB <= Aq -> Aq + k <= FB + 256 -> disjoint_from X0 Aq k) by (intros Aq k H1 H2; cbn; split; [clear - H1 H2 APPA; lia| exact I]).
    assert (DJs : forall Aq k, sp1 <= Aq -> disjoint_from X0 Aq k) by (intros Aq k H1; cbn; split; [clear - H1 ALO1 SP1 SLO NS1 STKg0 STKs0 STKf0 LOS ALO; unfold PKCS7_SIZE in *; lia| exact I]).
    apply (presA_shadow_cells_sh asegs R (hcs asegs R HIA hc) LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 FB _ (hcs_ok asegs R HIA hc)) in FSH;
      [| cbn [cells_size csize Nat.add]; exact CFBc | exact F8 | clear - F0; lia | exact HP4 | cbn [cells_size csize Nat.add]; intros c Hc; apply CSHD; clear - Hc; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 FB _ HP4) in FHD;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; left; reflexivity| clear; lia| clear; lia] | apply DJ; cbn [cells_size csize Nat.add]; clear; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 _ _ HP4) in G4;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJ; clear; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 _ _ HP4) in G8;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJ; clear; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 _ _ HP4) in G12;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJ; clear; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 _ _ HP4) in G16;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJ; clear; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 _ _ HP4) in G18;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJ; clear; lia ].
    apply (presA_rw_cells asegs R LB ((FB, 256) :: LF) sp1 (arl_stklo R) (hstkhi asegs R HIA h) X0 mc m4 _ _ HP4) in G22;
      [| cbn [cells_size csize Nat.add]; eapply client_range_block; [apply in_app_iff; right; right; left; reflexivity| clear; lia| clear; lia] | cbn [cells_size csize Nat.add]; apply DJ; clear; lia ].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m4 _ _ HP4) in SAVE; [| apply client_range_stack; clear - SP1; lia| apply DJs; clear - SP1; lia].
    apply (presA_rw_cells asegs R _ _ _ _ _ _ mc m4 _ _ HP4) in RSL; [| apply client_range_stack; clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m4 _ _ HP4) in STa; [| clear; lia| apply DJs; clear; lia].
    apply (presA_stk asegs R _ _ _ _ _ _ mc m4 _ _ HP4) in STb; [| clear; lia| apply DJs; clear; lia].
    apply (presA_sshad asegs R _ _ _ _ _ _ mc m4 _ _ HP4) in SSc; [| exact SLOS| clear - HT TOP; lia].
    assert (CRAs : client_range L (LB ++ fdata ((FB, 256) :: LF)) sp1 A 1440).
    { eapply client_range_lower; [| exact ALO1]. eapply client_range_incl; [exact (client_range_of_w L _ _ _ _ _ CWA)| intros b Hb; apply fdata_cons_sub; exact Hb]. }
    assert (OBJ4 : aobj asegs AL CS m4 A 1440).
    { eapply presA_aobj0; [exact CSOK| exact HP4| exact OBJA| intros x Hx; eapply hcs_below_top; exact Hx| right; split; [exact CRAs| clear - LOS SLO SP1 NS1 STKg0 STKs0 STKf0; lia]]. }
    assert (SIP4 : si_P SI m4).
    { eapply (si_heap_presx asegs L SI); [exact SIc| exact (presA_presx asegs R _ _ _ _ _ _ _ _ HP4)|]. intros a Ha. exact (si_outside1 L SI A 1440 a AOD Ha). }
    clear LAWS KINV.
    eapply (ret_walk FB sp1 W (PHIa + PHIf (Z.of_nat (length Lc))) (FFRa + FFRf (Z.of_nat (length Lc)) 0) w0 w1 w2 g4 g8 g12 g16 g18 g22 _ _ _ _ _ _ [CB 1440 (zeros 1440)]
              b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31
              LBx m4 mo4' h4 None r).
    - split; [exact HH4|]. split; [exact HK4|]. split; [eapply mo_frame_trans; [exact MFc| eapply mo_frame_trans; [exact MF1| exact MF4]]|].
      split; [exact HT4|]. split; [exact HS4|]. split; [exact HF4|]. split; [exact HCSh4|].
      split; [clear - HV4 HVc; lia|]. split; [clear - HFR4 HFRc; lia|].
      split; [exact PRES'|]. split; [exact SIP4|]. split; [exact SP1|]. split; [exact SP1M|]. split; [exact F64|]. split; [exact FRSH|]. split; [exact CFB|].
      split; [exact FHD|]. split; [exact G4|]. split; [exact G8|]. split; [exact G12|]. split; [exact G16|]. split; [exact G18|]. split; [exact G22|].
      split; [exact FSH|]. split; [exact SAVE|]. split; [exact RSL|].
      split; [exact STa|]. split; [exact STb|]. split; [exact ST4|].
      split; [unfold pkcs7_zero in PZ4; exact PZ4|]. split; [reflexivity|]. split; [exact OBJ4|]. split; [exact MI4|]. split; [exact SSc|].
      clear - C24f C24i. lia.
    - cbn. unfold pkcs7_zero in PZ4. split; [exact PZ4|]. split; [exact AAL|]. split; [exact A0|]. unfold RepCrt.PKCS7_SIZE. pose proof (rw_cells_bound _ _ _ _ PZ4) as B. cbn [cells_size csize Nat.add] in B. clear - B. lia.
    - exact I.
    - clear - CNT LEN4. lia.
    - exact PHI.
    - exact FFR.
    - exact HW.
    - exact Hr.
  Qed.
  End Call.
End Walk.
