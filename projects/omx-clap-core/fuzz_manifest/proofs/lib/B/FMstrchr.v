(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMstrchr.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* fm's runtime contract for the strchr interceptor in the donor's form: astrchr_realizes (lib/A/FMH_Rt.v:115) at
   PC_strchr = 0x41340, the four-byte jump to the interceptor at 0x42ee8 (REAL = musl strchr 0x92d9c).
   Proved inputs: A/Bz/A/I_strchrw.v tramp_strchr (the jump) and istrchr_spec (the interceptor, any character whose
   low byte is not zero), whose Section hypotheses are A/Bz/A/R_isPoisoned.v rip_proof and A/Prog/strchr_wrap.v
   chr_proof (musl strchr).  The walk's premises come from FMrt_pre.v, moved onto the CLEANED store
   (FMbz_clean.v: the walk's mem_inv holds there by construction, and the walk's run is carried back to the real
   store by bz_run_clean, whose read agreement is the contract's rom_viewN and rom_viewO); the post is read at the
   call site and turned into the donor-form post by FMbz_clean.rt_post_ro_win_clean over a Theorem Labs lane's FMrt_lift.v
   (rt_post_ro_win).  The walk reads the string up to the next 8-byte boundary after its NUL (musl's word loop):
   those bytes are cstr_ok's last clause. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YK0i YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.ReusableB Require Import YB1v YF0m YF0x.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A Require Import FMupoison.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMH_Base FMH_Rt FMrt_lift FMrt_pre FMbz_clean.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require ManifestModel.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.strchr_wrap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module RIP := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Bz.A.R_isPoisoned.
Module SWR := OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B.Prog.strchr_wrap.

(* ---- the walk's answer, read on the byte values ---- *)
Lemma find_idx_first : forall c (l : list Z) j,
  ManifestModel.find_idx (fun y => y =? c) l = Some j -> first_at l c j.
Proof.
  intros c l. induction l as [|y l IH]; intros j H; [discriminate|].
  cbn [ManifestModel.find_idx] in H. destruct (Z.eqb_spec y c) as [->|NE].
  - injection H as <-. split; [cbn; lia|]. split; [reflexivity|]. cbn [firstn]. intros [].
  - destruct (ManifestModel.find_idx (fun y0 => y0 =? c) l) as [j'|] eqn:E; cbn [option_map] in H; [|discriminate].
    injection H as <-. destruct (IH j' eq_refl) as (Hl & Hn & Hni).
    split; [cbn; lia|]. split; [exact Hn|]. cbn [firstn]. intros [Hc|Hc]; [exact (NE Hc) | exact (Hni Hc)].
Qed.

Lemma find_idx_none : forall c (l : list Z), ManifestModel.find_idx (fun y => y =? c) l = None -> ~ In c l.
Proof.
  intros c l. induction l as [|y l IH]; intros H; [intros []|].
  cbn [ManifestModel.find_idx] in H. destruct (Z.eqb_spec y c) as [E|NE]; [discriminate|].
  destruct (ManifestModel.find_idx (fun y0 => y0 =? c) l) eqn:E; cbn [option_map] in H; [discriminate|].
  intros [Hc|Hc]; [exact (NE Hc) | exact (IH eq_refl Hc)].
Qed.

(* the interceptor's result is the program part's: zero and c absent, or the string's address plus c's first index *)
Lemma chr_res_spec : forall x c (l : list Z), Forall (fun y => 0 <= y < 256) l ->
  (BCH.chr_res x c (map (Z_to_bv 8) l) = 0 /\ ~ In c l) \/
  (exists j, first_at l c j /\ BCH.chr_res x c (map (Z_to_bv 8) l) = x + Z.of_nat j).
Proof.
  intros x c l HR. unfold BCH.chr_res. rewrite (find_byte_map c l HR).
  destruct (ManifestModel.find_idx (fun y => y =? c) l) as [j|] eqn:E.
  - right. exists j. split; [exact (find_idx_first c l j E) | reflexivity].
  - left. split; [reflexivity | exact (find_idx_none c l E)].
Qed.

(* ---- the bytes after the NUL, up to the next 8-byte boundary ---- *)
Definition tail_bytes (m : word -> option byte) (a : Z) (k : nat) : list byte :=
  map (fun j => match BM.mrd BI.asegs m (BM.wa (a + Z.of_nat j)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 k).

Lemma tail_bytes_at : forall (m : word -> option byte) a k,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> BM.mrd BI.asegs m (BM.wa (a + i)) <> None) ->
  BM.bytes_at BI.asegs m a (tail_bytes m a k).
Proof.
  intros m a k Ha Hk HV. unfold tail_bytes.
  split; [exact Ha|]. split; [rewrite length_map, length_seq; exact Hk|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq.
  replace (i <? k)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi).
  cbn [option_map Nat.add].
  destruct (BM.mrd BI.asegs m (BM.wa (a + Z.of_nat i))) as [b|] eqn:E; [reflexivity|].
  exfalso. exact (HV (Z.of_nat i) ltac:(lia) E).
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.

Theorem astrchr_holds : astrchr_realizes tfibsegs B PC_strchr.
Proof.
  unfold astrchr_realizes. intros ly S W regs mem md x c l HPRE HROM HROMO G10 G11 Hc HCS.
  pose proof HCS as (HCSTR & Hx4096 & HxE & H32 & Ham & HRA & HV & HTAIL).
  pose proof HPRE as ((HAR & _) & _).
  pose proof (rom_eq_of_views B W mem TB HROM HROMO) as RE.
  assert (HSTK : STK_RT_STR = 8192) by reflexivity.
  destruct (stk_of_pre B ly S W regs mem md STK_RT_STR HPRE ltac:(lia)) as (ST0 & HC0 & HC1 & HSP).
  assert (ST : BF.stk BI.asegs (clean (mrestrict (w_H W) mem)) (spZ regs - STK_RT_STR) (spZ regs)).
  { apply (stk_clean (mrestrict (w_H W) mem) (spZ regs - STK_RT_STR) (spZ regs));
      [unfold TFIB_IMG_END; lia | unfold BM.UTOP; lia | exact ST0]. }
  pose proof (mem_inv_clean (mrestrict (w_H W) mem)) as MI.
  pose proof (m2s_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as M2S.
  pose proof (icells_chr_of_ARm_clean B TB ly S (w_H W) mem RE (proj1 HAR)) as IC.
  assert (Esp : bv_unsigned (reg_get regs 2) = spZ regs) by reflexivity.
  assert (E11 : bv_unsigned (reg_get regs 11) mod 256 = c).
  { change (reg_get regs 11) with (getr regs 11). rewrite G11. unfold w64. rewrite u64z by lia.
    apply Z.mod_small. lia. }
  destruct (bytes_of_cstr W mem x l HCSTR ltac:(lia) ltac:(lia)) as (BUF0 & NZ & HR).
  assert (HR8 : Forall (fun y => 0 <= y < 256) l)
    by (apply (Forall_impl _ (fun y (H : 0 <= y < 256 /\ y <> 0) => proj1 H) HR)).
  (* the string, its NUL and the rest of the NUL's 8-byte word, as the walk reads them *)
  remember (Z.of_nat (length l)) as len eqn:Elen.
  set (k := Z.to_nat (7 - (x + len) mod 8)).
  assert (K7 : Z.of_nat k = 7 - (x + len) mod 8) by (unfold k; rewrite Z2Nat.id; [reflexivity | Z.div_mod_to_equations; lia]).
  set (slack := tail_bytes (mrestrict (w_H W) mem) (x + len + 1) k).
  assert (BSL : BM.bytes_at BI.asegs (mrestrict (w_H W) mem) (x + len + 1) slack).
  { apply tail_bytes_at; [lia | lia |]. intros i Hi.
    assert (HN : aview tfibsegs (w_H W) mem (x + len + 1 + i) <> None).
    { apply HTAIL. Z.div_mod_to_equations. lia. }
    apply (proj1 (YF0x.aview_vis (w_H W) mem _)) in HN. rewrite mrd_mbyte. exact HN. }
  set (str := map (Z_to_bv 8) l) in *.
  assert (LS : length str = length l) by apply length_map.
  assert (BUFm : BM.bytes_at BI.asegs (mrestrict (w_H W) mem) x (str ++ Z_to_bv 8 0 :: slack)).
  { replace (str ++ Z_to_bv 8 0 :: slack) with ((str ++ [Z_to_bv 8 0]) ++ slack) by (rewrite <- app_assoc; reflexivity).
    apply (proj2 (BM.bytes_at_app BI.asegs _ x _ _)). split; [exact BUF0|].
    rewrite length_app, LS. cbn [length]. replace (x + Z.of_nat (length l + 1)) with (x + len + 1) by lia. exact BSL. }
  assert (LL : Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) = len + 1 + Z.of_nat k).
  { rewrite length_app, LS. cbn [length]. unfold slack, tail_bytes. rewrite length_map, length_seq. lia. }
  pose proof (BCH.chr_n_le x c str) as NL. pose proof (BCH.chr_n_ge x c str) as NG.
  rewrite LS, <- Elen in NL.
  assert (PM : (- (x + (len + 1))) mod 8 = 7 - (x + len) mod 8) by (Z.div_mod_to_equations; lia).
  pose proof (BCH.pad_mono2 x (BCH.chr_n x c str) (len + 1) NL) as PAD.
  assert (BUF : BM.bytes_at BI.asegs (clean (mrestrict (w_H W) mem)) x (str ++ Z_to_bv 8 0 :: slack)).
  { apply (bytes_at_clean _ x _ RE); [rewrite LL; unfold BM.UTOP, STK_RT_STR, ESTACK in *; lia | exact BUFm]. }
  eapply (bz_run_clean B TB W PC_strchr regs mem md _ _ HROM HROMO).
  - apply bz_canon. apply BCH.tramp_strchr.
    eapply (BCH.istrchr_spec RIP.rip_proof SWR.chr_proof)
      with (s := x) (str := str) (slack := slack) (L := length (str ++ Z_to_bv 8 0 :: slack))
           (lo := spZ regs - STK_RT_STR);
      [ exact G10
      | exact ST
      | rewrite Esp; lia
      | unfold BR.kHighShadowEnd; lia
      | rewrite Esp; lia
      | lia
      | rewrite LL; lia
      | rewrite firstn_all; exact BUF
      | exact NZ
      | rewrite length_app; cbn [length]; lia
      | rewrite E11; lia
      | rewrite E11, LL; lia
      | left; rewrite LL, Esp; lia
      | rewrite E11; apply (chk_ok_clean _ x _ RE);
        [ lia
        | unfold STK_RT_STR, ESTACK in *; lia
        | apply (chk_ok_of_cstr B ly S W mem md x l _ HAR HCS); lia ]
      | exact M2S
      | exact IC
      | exact MI ].
  - intros msc ms' model' HQ Hcl Heqv Hsbm _.
    destruct HQ as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & MI' & ST').
    rewrite E11 in Heqv. rewrite E11 in Hcl.
    destruct (bz_window (clean (mrestrict (w_H W) mem)) m' (spZ regs) 2224 (spZ regs - STK_RT_STR) MU ST'
                ltac:(lia) ltac:(unfold TFIB_IMG_END; lia)) as (MOUT & MIN).
    pose proof (chr_res_spec x c l HR8) as VR. fold str in VR.
    eapply (rt_post_ro_win_clean B LAWS STK_RT_STR 2224 ly S W regs mem md _ _ ms' model' (BCH.chr_res x c str) HPRE
              ltac:(lia) Hcl Heqv Hsbm);
      try reflexivity.
    + keep_regs.
    + destruct VR as [(-> & _) | (j & (Hj & _ & _) & ->)]; lia.
    + exact VR.
    + exact MOUT.
    + exact MIN.
Qed.

End s.
