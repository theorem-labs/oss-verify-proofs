(* fm's runtime contract for memchr (p, 0, n) in the donor's form: amemchr_realizes (lib/A/FMH_Rt.v:143) at
   PC_memchr = 0x412ec, the four-byte jump to the interceptor at 0x43b78 (REAL = musl memchr 0x924a8), in both
   cases: a zero byte found (result p + its index) and none (result 0).
   Proved inputs: A/Bz/A/I_tramp.v tramp_memchr (the jump) and A/Bz/A/I_memchrw.v imemchr_spec (the interceptor),
   whose Section hypotheses are A/Bz/A/R_isPoisoned.v rip_proof and A/Prog/wrap_kit.v mch_proof (musl memchr).
   The walk's premises come from FMrt_pre.v; it is read at the call site and turned into the donor-form post by
   a Theorem Labs lane's FMrt_lift.v (srr_of_canon_bz, rt_post_ro_win). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import
AB1v AF0m AF0x FMupoison FMH_Base FMH_Rt FMrt_lift FMrt_pre FMbz_clean.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_tramp.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.wrap_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module TRP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Bz.A.R_isPoisoned.
Module WK := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Prog.wrap_kit.

(* ---- the walk's answer, read on the byte values ---- *)
Lemma find_idx_lt : forall (f : Z -> bool) (l : list Z) k, ManifestModel.find_idx f l = Some k -> (k < length l)%nat.
Proof.
  intros f l. induction l as [|y l IH]; intros k H; [discriminate|].
  cbn [ManifestModel.find_idx] in H. destruct (f y).
  - injection H as <-. cbn. lia.
  - destruct (ManifestModel.find_idx f l) as [k'|] eqn:E; cbn [option_map] in H; [|discriminate].
    injection H as <-. pose proof (IH k' eq_refl). cbn. lia.
Qed.

Lemma firstn_len : forall (l : list Z),
  firstn (Z.to_nat (Z.of_nat (length l))) (map (Z_to_bv 8) l) = map (Z_to_bv 8) l.
Proof. intros l. rewrite Nat2Z.id. apply firstn_all2. rewrite length_map. lia. Qed.

(* the interceptor's result is the program part's: p plus the first zero's index, or 0 *)
Lemma memchr_res_spec : forall x (l : list Z), Forall (fun y => 0 <= y < 256) l ->
  BSF.memchr_res x 0 (Z.of_nat (length l)) (map (Z_to_bv 8) l) =
  match ManifestModel.find_idx (fun c => c =? 0) l with Some k => x + Z.of_nat k | None => 0 end.
Proof.
  intros x l HR. unfold BSF.memchr_res. rewrite firstn_len, (find_byte_map 0 l HR). reflexivity.
Qed.

(* and the length its range check reads is the program part's mchr_len *)
Lemma memchr_len_spec : forall x (l : list Z), 0 < x -> Forall (fun y => 0 <= y < 256) l ->
  BMC.memchr_len x 0 (Z.of_nat (length l)) (map (Z_to_bv 8) l) = mchr_len l.
Proof.
  intros x l Hx HR. unfold BMC.memchr_len, mchr_len. rewrite (memchr_res_spec x l HR).
  destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [k|].
  - replace (x + Z.of_nat k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). lia.
  - reflexivity.
Qed.

Lemma mchr_len_bounds : forall (l : list Z), 0 <= mchr_len l <= Z.of_nat (length l).
Proof.
  intros l. unfold mchr_len. destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [k|] eqn:E; [|lia].
  pose proof (find_idx_lt _ l k E). lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.

Theorem amemchr_holds : amemchr_realizes tfibsegs B PC_memchr.
Proof.
  unfold amemchr_realizes. intros ly S W regs mem md x n l HPRE HROM HROMO G10 G11 G12 Hn HB Hlen Hx HxE Ham HRA HV.
  subst n.
  pose proof HPRE as ((HAR & _) & _).
  pose proof (rom_eq_of_views B W mem TB HROM HROMO) as RE.
  assert (HSTK : STK_RT_STR = 8192) by reflexivity.
  destruct (stk_of_pre B ly S W regs mem md STK_RT_STR HPRE ltac:(lia)) as (ST0 & HC0 & HC1 & HSP).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - STK_RT_STR) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - STK_RT_STR) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_mc_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  destruct (bytes_of_bytes_at W mem x l HB ltac:(lia) ltac:(lia)) as (BUFm & HR).
  pose proof (memchr_len_spec x l ltac:(lia) HR) as ML.
  pose proof (mchr_len_bounds l) as MB.
  set (buf := map (Z_to_bv 8) l) in *.
  assert (LB : length buf = length l) by apply length_map.
  assert (BUF : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x buf).
  { apply (bytes_at_clean _ x _ RE); [rewrite LB; unfold BM.UTOP, STK_RT_STR, ESTACK in *; lia | exact BUFm]. }
  eapply (bz_run_clean B TB W PC_memchr regs mem md _ _ HROM HROMO).
  - apply bz_canon. apply TRP.tramp_memchr.
    eapply (BMC.imemchr_spec RIP.rip_proof WK.mch_proof)
      with (s := x) (cz := 0) (n := Z.of_nat (length l)) (buf := buf) (lo := spZ regs - STK_RT_STR);
      [ exact G10
      | exact G11
      | exact G12
      | exact ST
      | rewrite Esp; lia
      | unfold BR.kHighShadowEnd; lia
      | rewrite Esp; lia
      | lia
      | lia
      | lia
      | change (0 mod 256) with 0; rewrite ML; lia
      | exact BUF
      | change (0 mod 256) with 0; unfold BSF.memchr_ok;
        destruct (BSF.find_byte 0 (firstn (Z.to_nat (Z.of_nat (length l))) buf)); [left|]; rewrite LB; lia
      | left; rewrite LB, Esp; lia
      | change (0 mod 256) with 0; rewrite ML; apply (chk_ok_clean _ x _ RE);
        [ lia
        | unfold STK_RT_STR, ESTACK in *; lia
        | apply (chk_ok_of_pre B ly S W mem md x (mchr_len l) HAR);
          [ lia | lia | apply (amem_range_mono _ _ _ Ham); lia | exact HRA | intros Hp; apply HV; lia ] ]
      | exact M2S
      | exact IC
      | exact MI ].
  - intros msc ms' model' HQ Hcl Heqv Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST').
    change (0 mod 256) with 0 in Heqv.
    destruct (bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 2208 (spZ regs - STK_RT_STR) MU ST'
                ltac:(lia) ltac:(unfold TFIB_IMG_END; lia)) as (MOUT & MIN).
    pose proof (memchr_res_spec x l HR) as VR. fold buf in VR.
    eapply (rt_post_ro_win_clean B LAWS STK_RT_STR 2208 ly S W regs mem md _ _ ms' model'
              (BSF.memchr_res x 0 (Z.of_nat (length l)) buf) HPRE ltac:(lia) Hcl Heqv Hsbm);
      try reflexivity.
    + keep_regs.
    + rewrite VR. destruct (ManifestModel.find_idx (fun c => c =? 0) l) as [k|] eqn:E; [|lia].
      pose proof (find_idx_lt _ l k E). lia.
    + cbv beta. rewrite VR. destruct (ManifestModel.find_idx (fun c => c =? 0) l); reflexivity.
    + exact MOUT.
    + exact MIN.
Qed.

End s.
