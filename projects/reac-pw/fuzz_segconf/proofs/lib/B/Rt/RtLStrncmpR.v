(* OUR contract of the strncmp interceptor (lib/A/Rt/RtString.v astrncmp_realizes) from the same committed walk as
   fuzz_manifest's statement of record (lib/A/Rt/RtLStrncmp.v astrncmp_holds): a SIBLING lift, not a corollary. Neither
   statement implies the other: fuzz_manifest's cstr_ok (RtBzHBase.v:44-50) asks of each string what ours does not give
   (4096 <= p, p + len + 8 <= alloc_ceiling, and the range and shadow facts over the WHOLE string, where ours are
   over min (n, len + 1)), and ours asks for a read of only min (n, len + 1) bytes, which fuzz_manifest's does not state.
   Both are proved here from B/Bz/A/I_strncmp.v istrncmp_spec at the trampoline B/Bz/A/I_tramp.v tramp_strncmp
   (0x4518c -> 0x45fa4), through the relocated bridge (RtBz*.v) and our adapter (RtBzAdapt*.v).

   Two things are ours rather than fuzz_manifest's:
   - the compared length: the walk reads only strncmp_sz n b1 b2 bytes of each string, so the byte lists it is
     given are the strings TRUNCATED to that length (I_strncmp.v:34 sc_trunc keeps the answer), and our aread_ok
     over min (n, len + 1) bytes is enough for them. For n = 0 the walk's own n = 0 branch (I_strncmp.v:203
     isc_zero) is used, which asks nothing of the strings - our contract says nothing about them there either.
   - the answer: the walk's strncmp_res is 0 exactly when the plain proof's strncmp_model is Some 0
     (lib/Spec/StrFun.v), through RtLStrncmp.strncmp_strs and model_zero_iff below. *)
(* The image-B twin of lib/A/Rt/RtLStrncmpR.v, for fuzz_command.asan-ubsan (no function proved): the B
   kit's walk (lib/B/Bz), B's contract (lib/B/Rt/RtString.v), the B bridge and adapter, and every A address replaced
   by its B twin (each re-read from image B); the proof text is the A file's. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YK04 YK0i YK14 YK1b YP03 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0n YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YI04 YK06 YM05.


From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtBzHBase RtBzHStr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtString RtBzLift RtBzPre RtBzClean RtBzAdapt RtBzAdaptP RtLStrncmp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require StrFun.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.IcptSpec.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmpw3.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmp.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_tramp.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PStrFun := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.StrFun.
Module SCS := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.IcptSpec.
Module SCP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmpw3.
Module SCW := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_strncmp.
Module TRP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.I_tramp.
Module RIP := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.A.R_isPoisoned.
Module BzX := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Bz.Lib.Exec.

(* ---- byte lists ---- *)

Lemma map_bv_roundtrip : forall s : list byte, map (Z_to_bv 8) (map (fun b : byte => bv_unsigned b) s) = s.
Proof.
  induction s as [|b s IH]; [reflexivity|].
  cbn [map]. rewrite IH. f_equal. apply Z_to_bv_bv_unsigned.
Qed.

Lemma bytes_nz_forall : forall s : list byte, ~ In (Z_to_bv 8 0) s ->
  Forall (fun c => 0 <= c < 256 /\ c <> 0) (map (fun b : byte => bv_unsigned b) s).
Proof.
  intros s HN. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (bb & <- & Hin).
  pose proof (bv_unsigned_in_range 8 bb) as HR. unfold bv_modulus in HR. cbn [Z.of_N] in HR.
  change (2 ^ 8) with 256 in HR.
  split; [lia|]. intros E. apply HN.
  replace (Z_to_bv 8 0) with bb; [exact Hin | apply bv_eq; rewrite E; reflexivity].
Qed.

Lemma nth_firstn_lt : forall (l : list byte) j i d, (i < j)%nat -> nth i (firstn j l) d = nth i l d.
Proof.
  induction l as [|b l IH]; intros j i d Hi; [rewrite firstn_nil; destruct i; reflexivity|].
  destruct j as [|j]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma abytes_firstn : forall (W : world tfibsegs) mem a (l : list byte) j,
  abytes_at tfibsegs W mem a l -> abytes_at tfibsegs W mem a (firstn j l).
Proof.
  intros W mem a l j HB i Hi. rewrite length_firstn in Hi.
  rewrite nth_firstn_lt by lia. apply HB. lia.
Qed.

(* ---- the walk's answer and the plain proof's model are the same claim ----
   (the only other copy of these two list facts in this tree was lib/A/Rt/RtSStrncmpBridge.v, an untracked
   measurement file that does not compile and is being deleted, so they are proved here) *)

Lemma nul_of_u0 : forall a : byte, bv_unsigned a = 0 -> a = Z_to_bv 8 0.
Proof. intros a H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma walk_zero_iff : forall (sa sb : list byte) (k : nat),
  ~ In (Z_to_bv 8 0) sa -> ~ In (Z_to_bv 8 0) sb ->
  (PStrFun.strncmp_walk (sa ++ [Z_to_bv 8 0]) (sb ++ [Z_to_bv 8 0]) k = Some 0 <->
   firstn (S k) (map (fun b : byte => bv_unsigned b) (sa ++ [Z_to_bv 8 0])) =
   firstn (S k) (map (fun b : byte => bv_unsigned b) (sb ++ [Z_to_bv 8 0]))).
Proof.
  induction sa as [|p sa IH]; intros sb k Na Nb.
  - destruct sb as [|q sb].
    + cbn. split; intros _; [reflexivity|]. destruct k; reflexivity.
    + cbn [app map firstn PStrFun.strncmp_walk].
      assert (Hq : bv_unsigned q <> 0) by (intros E; apply Nb; left; exact (nul_of_u0 q E)).
      change (bv_unsigned (Z_to_bv 8 0)) with 0. cbn [Z.eqb orb].
      split; intros H; [injection H as H; lia | injection H as H _; lia].
  - assert (Hp : bv_unsigned p <> 0) by (intros E; apply Na; left; exact (nul_of_u0 p E)).
    destruct sb as [|q sb].
    + cbn [app map firstn PStrFun.strncmp_walk]. change (bv_unsigned (Z_to_bv 8 0)) with 0.
      replace ((bv_unsigned p =? 0) || (0 =? 0) || Nat.eqb k 0 || negb (bv_unsigned p =? 0))%bool with true
        by (rewrite Z.eqb_refl, !Bool.orb_true_r; reflexivity).
      split; intros H; [injection H as H; lia | injection H as H _; lia].
    + assert (Hq : bv_unsigned q <> 0) by (intros E; apply Nb; left; exact (nul_of_u0 q E)).
      assert (Na' : ~ In (Z_to_bv 8 0) sa) by (intros H; apply Na; right; exact H).
      assert (Nb' : ~ In (Z_to_bv 8 0) sb) by (intros H; apply Nb; right; exact H).
      cbn [app map firstn PStrFun.strncmp_walk].
      rewrite (proj2 (Z.eqb_neq _ _) Hp), (proj2 (Z.eqb_neq _ _) Hq). cbn [orb].
      destruct k as [|k].
      * cbn [Nat.eqb orb firstn]. split; intros H.
        -- injection H as H. f_equal. lia.
        -- injection H as H. rewrite H. f_equal. lia.
      * cbn [Nat.eqb orb].
        destruct (Z.eq_dec (bv_unsigned p) (bv_unsigned q)) as [Epq|Npq].
        -- rewrite Epq, Z.eqb_refl. cbn [negb]. rewrite (IH sb k Na' Nb').
           split; [intros H; rewrite H; reflexivity | intros H; injection H as H; exact H].
        -- rewrite (proj2 (Z.eqb_neq _ _) Npq). cbn [negb].
           split; intros H; [injection H as H; lia | injection H as H _; lia].
Qed.

Theorem model_zero_iff : forall (sx sy : list byte) (n : Z), 0 <= n ->
  ~ In (Z_to_bv 8 0) sx -> ~ In (Z_to_bv 8 0) sy ->
  (PStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0 <->
   strn_eq (Z.to_nat n) (map (fun b : byte => bv_unsigned b) sx) (map (fun b : byte => bv_unsigned b) sy)).
Proof.
  intros sx sy n Hn Nx Ny. unfold PStrFun.strncmp_model, strn_eq.
  assert (Ex : map (fun b : byte => bv_unsigned b) sx ++ [0]
               = map (fun b : byte => bv_unsigned b) (sx ++ [Z_to_bv 8 0])) by (rewrite map_app; reflexivity).
  assert (Ey : map (fun b : byte => bv_unsigned b) sy ++ [0]
               = map (fun b : byte => bv_unsigned b) (sy ++ [Z_to_bv 8 0])) by (rewrite map_app; reflexivity).
  rewrite Ex, Ey.
  destruct (Z.eqb_spec n 0) as [->|Hn0].
  - cbn. split; intros _; reflexivity.
  - replace (Z.to_nat n) with (S (Z.to_nat (n - 1))) by lia. apply walk_zero_iff; assumption.
Qed.

(* n = 0: the walk compares nothing and answers 0 *)
Lemma idx_zero : forall b1 b2, SCS.strncmp_idx 0 b1 b2 = 0.
Proof. intros b1 b2. unfold SCS.strncmp_idx. change (Z.to_nat 0) with O. destruct b1; reflexivity. Qed.

Lemma res_zero : forall b1 b2, SCS.strncmp_res 0 b1 b2 = 0.
Proof. intros b1 b2. unfold SCS.strncmp_res. rewrite (idx_zero b1 b2). reflexivity. Qed.

Lemma sz_zero : forall b1 b2, SCS.strncmp_sz 0 b1 b2 = 0.
Proof. intros b1 b2. unfold SCS.strncmp_sz. rewrite (idx_zero b1 b2). reflexivity. Qed.

(* ---- the contract ---- *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : SegBSyms B.

(* RtString.astrncmp_realizes, qualified: RtBzHStr (fuzz_manifest's statement) defines the same name *)
Theorem cmd_strncmp : RtString.astrncmp_realizes tfibsegs B 0x43aa4.
Proof.
  unfold RtString.astrncmp_realizes.
  intros ly S W regs mem md x y n sx sy HPRE G10 G11 G12 Hn Hx Hy SX SY RDX AMX RDY AMY TX TY HROM.
  pose proof HPRE as (HEP & HSLO & HPRS).
  pose proof HEP as (HAR & _).
  pose proof RDX as (RX0 & RX1 & RX2 & _).
  pose proof RDY as (RY0 & RY1 & RY2 & _).
  pose proof AMX as AMX'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMX'.
  pose proof AMY as AMY'. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in AMY'.
  unfold astr_len in *.
  (* ---- the answer ---- *)
  pose proof (bytes_nz_forall sx (proj2 SX)) as F1.
  pose proof (bytes_nz_forall sy (proj2 SY)) as F2.
  destruct (strncmp_strs n (map (fun b : byte => bv_unsigned b) sx)
              (map (fun b : byte => bv_unsigned b) sy) ltac:(lia) F1 F2) as (OK & SZ1 & SZ2 & RES).
  rewrite !map_bv_roundtrip in OK. rewrite !map_bv_roundtrip, !length_map in SZ1.
  rewrite !map_bv_roundtrip, !length_map in SZ2. rewrite !map_bv_roundtrip in RES.
  assert (ANS : SCS.strncmp_res n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) = 0 <->
                PStrFun.strncmp_model (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) n = Some 0).
  { rewrite RES. symmetry.
    exact (model_zero_iff sx sy n ltac:(lia) (proj2 SX) (proj2 SY)). }
  assert (SZN : SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) <= n)
    by (unfold SCS.strncmp_sz; lia).
  assert (SZ0 : 0 <= SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
    by (unfold SCS.strncmp_sz, SCS.strncmp_idx; lia).
  (* ---- the cleaned store ---- *)
  pose proof (rom_eq_of_rt B TB ly S W mem md HAR HROM) as RE.
  pose proof (RtBzClean.mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  destruct (stk_of_stk_pre B (2 * ESTACK) ly S W regs mem md HPRE ltac:(unfold ESTACK; lia))
    as (ST0 & HC0 & HCs & Hsp47).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - 2 * ESTACK) (spZ regs)).
  { apply (RtBzClean.stk_clean (mrestrict (w_H W) mem) (spZ regs - 2 * ESTACK) (spZ regs));
      [unfold TFIB_IMG_END, ESTACK in *; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_sc_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  (* ---- the run ---- *)
  apply (RtBzClean.bz_run_clean B TB W 0x43aa4 regs mem md
           (fun ms1 => SCP.istrncmp_post (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
              (reg_get regs 8) (reg_get regs 9) (reg_get regs 18) (reg_get regs 19) (reg_get regs 20)
              (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24) (reg_get regs 25)
              (reg_get regs 26) (reg_get regs 27) fp_regs fp_csr
              (SCS.strncmp_res n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
              (spZ regs - 2 * ESTACK) (clean (mrestrict (w_H W) mem)) ms1
            /\ YK1b.mem_grows (clean (mrestrict (w_H W) mem)) (ms_mem ms1)) _
           (romN_of_rt B W mem HROM) (rom_viewO_of_ARm B TB ly S W mem (proj1 HAR))).
  - apply RtBzAdaptP.evt_grows. apply RtBzPre.bz_canon. apply TRP.tramp_strncmp.
    destruct (Z.eq_dec n 0) as [->|Hn0].
    + (* n = 0: the walk's own zero branch asks nothing of the strings *)
      rewrite (res_zero (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])).
      apply (SCW.isc_zero (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9)
               (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14)
               (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19)
               (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
               (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
               (reg_get regs 30) (reg_get regs 31) fp_regs fp_csr (clean (mrestrict (w_H W) mem)) x y
               (spZ regs - 2 * ESTACK));
        [exact G10 | exact G11 | exact G12
         | exact ST
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); unfold ESTACK in *; lia
         | unfold BR.kHighShadowEnd; lia
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); lia
         | lia | lia | exact IC | exact MI].
    + (* 0 < n: the strings, truncated to the compared length *)
      destruct (SCW.sc_trunc n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]) ltac:(lia) OK)
        as (EIc & ERc & ESc & OKc & LC1 & LC2).
      rewrite <- ERc.
      apply (SCW.istrncmp_spec RIP.rip_proof (reg_get regs 1) (reg_get regs 2) (reg_get regs 3) (reg_get regs 4)
               (reg_get regs 5) (reg_get regs 6) (reg_get regs 7) (reg_get regs 8) (reg_get regs 9)
               (reg_get regs 10) (reg_get regs 11) (reg_get regs 12) (reg_get regs 13) (reg_get regs 14)
               (reg_get regs 15) (reg_get regs 16) (reg_get regs 17) (reg_get regs 18) (reg_get regs 19)
               (reg_get regs 20) (reg_get regs 21) (reg_get regs 22) (reg_get regs 23) (reg_get regs 24)
               (reg_get regs 25) (reg_get regs 26) (reg_get regs 27) (reg_get regs 28) (reg_get regs 29)
               (reg_get regs 30) (reg_get regs 31) fp_regs fp_csr (clean (mrestrict (w_H W) mem)) x y n
               (firstn (Z.to_nat (SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])))
                  (sx ++ [Z_to_bv 8 0]))
               (firstn (Z.to_nat (SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])))
                  (sy ++ [Z_to_bv 8 0]))
               (spZ regs - 2 * ESTACK));
        [exact G10 | exact G11 | exact G12 | exact ST
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); unfold ESTACK in *; lia
         | unfold BR.kHighShadowEnd; lia
         | change (bv_unsigned (reg_get regs 2)) with (spZ regs); lia
         | lia | | | exact OKc | | | | | | | exact M2S | exact IC | exact MI].
      * (* the first string's bytes, on the cleaned store *)
        apply (RtBzClean.bytes_at_clean (mrestrict (w_H W) mem) x _ RE);
          [rewrite LC1; unfold BM.UTOP; lia|].
        apply bz_bytes_of_abytes; [apply abytes_firstn; exact (proj1 SX) | lia | rewrite LC1; lia].
      * apply (RtBzClean.bytes_at_clean (mrestrict (w_H W) mem) y _ RE);
          [rewrite LC2; unfold BM.UTOP; lia|].
        apply bz_bytes_of_abytes; [apply abytes_firstn; exact (proj1 SY) | lia | rewrite LC2; lia].
      * rewrite ESc. lia.
      * rewrite ESc. lia.
      * rewrite ESc. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
        destruct (sep_of_read (2 * ESTACK) W regs mem x (Z.min n (Z.of_nat (length sx) + 1))
                    ltac:(unfold ESTACK; lia) ltac:(lia) RDX) as [HL|HR];
          [left; unfold ESTACK in *; lia | right; lia].
      * rewrite ESc. change (bv_unsigned (reg_get regs 2)) with (spZ regs).
        destruct (sep_of_read (2 * ESTACK) W regs mem y (Z.min n (Z.of_nat (length sy) + 1))
                    ltac:(unfold ESTACK; lia) ltac:(lia) RDY) as [HL|HR];
          [left; unfold ESTACK in *; lia | right; lia].
      * rewrite ESc.
        apply (RtBzClean.chk_ok_clean (mrestrict (w_H W) mem) x
                 (SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) RE ltac:(lia) ltac:(lia)).
        exact (chk_of_read (2 * ESTACK) W regs mem x (Z.min n (Z.of_nat (length sx) + 1))
                 (SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
                 (Z.of_nat (length sx)) RDX AMX ltac:(lia) ltac:(lia) ltac:(lia)).
      * rewrite ESc.
        apply (RtBzClean.chk_ok_clean (mrestrict (w_H W) mem) y
                 (SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) RE ltac:(lia) ltac:(lia)).
        exact (chk_of_read (2 * ESTACK) W regs mem y (Z.min n (Z.of_nat (length sy) + 1))
                 (SCS.strncmp_sz n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0]))
                 (Z.of_nat (length sy)) RDY AMY ltac:(lia) ltac:(lia) ltac:(lia)).
  - (* ---- the post ---- *)
    intros msc ms' model' (HQ & GROW) Hcl Heqv Hsbm _.
    unfold SCP.istrncmp_post in HQ.
    destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM
                    & MI' & ST').
    destruct (RtBzPre.bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 2256
                (spZ regs - 2 * ESTACK) MU ST') as (MO & MN);
      [unfold ESTACK; lia | unfold TFIB_IMG_END, ESTACK in *; lia |].
    apply (RtBzAdaptP.art_post_ro_clean B LAWS (2 * ESTACK) 2256 ly S W regs mem md _ _ ms' model' HPRE
             ltac:(unfold ESTACK; lia) Hcl Heqv Hsbm
             eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl ltac:(keep_regs) MO MN GROW).
    intros regs' mem' HR _.
    assert (A10 : getr regs' 10%bv
                  = Z_to_bv 64 (SCS.strncmp_res n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])))
      by (rewrite (HR 10%bv); reflexivity).
    rewrite A10.
    split.
    + intros E. apply ANS.
      apply (f_equal (fun w : word => bv_unsigned w)) in E. unfold w64 in E.
      rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E.
      change (bv_modulus 64) with (2 ^ 64) in E.
      rewrite (Z.mod_small 0 (2 ^ 64) ltac:(lia)) in E.
      pose proof (strncmp_res_range n (sx ++ [Z_to_bv 8 0]) (sy ++ [Z_to_bv 8 0])) as Hr.
      revert E. Z.div_mod_to_equations. lia.
    + intros E. apply ANS in E. rewrite E. reflexivity.
Qed.

End s.
