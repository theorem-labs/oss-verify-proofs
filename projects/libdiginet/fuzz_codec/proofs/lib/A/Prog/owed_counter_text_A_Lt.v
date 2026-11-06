(* owed_counter_text at image A: the tactics of the first loop's step (lib/A/Prog/owed_counter_text_A_L<k>.v use
   them, one lemma per n). One step from the loop head 0x83f48 (ss_L n, INV_L n): the text byte t[i] (atom 350, its
   region based at the cursor, atom 300, and its shadow entry), then
   - c = 0: 0x8405c, the second loop (ss_Z n, INV_Z n);
   - c = '.', n > 0, dot[n - 1] = 0: dot[n - 1] := 1, the next character (ss_L n);
   - otherwise owed_seg7 (c, or ' ' for '.') at 0x8438c through its contract (CPgWalkCall.cpw_call_reseat_at, the callee's
     sp sp1), v = its result in atom 310 + n; v < 0 or n = 8: the release with SPEC_E_RANGE (ss_R (2^64 - 11));
     else dot[n] := (c = '.') (atom 320 + n) and s[n] := v, the next character (ss_L (n + 1)). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require AE36.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


(* a region of the walk kept across the owed_seg7 call (K the callee post's tcj_kept, J2 the post journal) *)
Ltac oc_kept_call K J1 J2 :=
  idtac;
  lazymatch goal with |- region_kept _ ?Ev _ _ (YP09.mkRegion (Some ?n) ?lo ?hi ?wlo ?whi _) =>
  lazymatch eval cbv in (orb (Nat.eqb n 2) (Nat.eqb n 70)) with
  | true =>
    lazymatch goal with Lx : AR_laws _ ?Bv |- _ =>
    eapply (region_kept_tcj_stack Bv);
    [ exact K
    | first [ eassumption | lazymatch goal with E70x : ew Ev 70 = Z_to_bv 64 _ |- _ => rewrite E70x; apply unsigned_lit_small; lia end ]
    | intros ? ?; unfold T_owed_counter_text, ESTACK in *; split; [lia | split; [lia | intros []]]
    | intros ? ?; unfold T_owed_counter_text, ESTACK in *; split; lia ] end
  | false =>
    lazymatch goal with Lx : AR_laws _ ?Bv, HFRSx : frames ?S3x = (1, ?ps) :: _,
      EFAx : forall c p, frame_addr ?ly3x c p = frame_addr ?lcx c p, HFx : ?Fv = frame_addr ?lcx 1 ?ps |- _ =>
    first [eapply (region_kept_tcj_frame Bv) with (cid := 1) (pos := ps) | idtac "KF-APPLY"; fail];
    [ first [exact K | idtac "KF-K"; fail]
    | first [ lazymatch goal with E75x : ew Ev 75 = Z_to_bv 64 _ |- _ => rewrite E75x; apply unsigned_lit_small; lia end
            | lazymatch goal with E88x : ew Ev 88 = Z_to_bv 64 _ |- _ => rewrite E88x; apply unsigned_lit_small; unfold SB; lia end
            | match goal with |- ?g => idtac "KF-BASE" g; fail end ]
    | first [rewrite HFRSx; left; reflexivity | match goal with |- ?g => idtac "KF-IN" g; fail end]
    | first [rewrite EFAx, <- HFx; change (fs_frame_bytes 1) with 128;
      first [left; lia | right; unfold shadow_addr; rewrite <- SB_SHADOW_OFF; change (128 / 8) with 16; lia] | match goal with |- ?g => idtac "KF-RNG" g; fail end]
    | first [intros ? ? [] | idtac "KF-E"; fail]
    | first [ intros ? ?; exfalso; lia
            | lazymatch type of J2 with ajournal _ _ _ _ _ _ _ _ _ _ _ ?ly2 ?S2 _ _ _ _ =>
              lazymatch goal with Hf : frames S2 = frames S3x |- _ =>
              let Hin2 := fresh "Hin2" in let Hp := fresh "Hp" in
              assert (Hin2 : In (1, ps) (frames S2)) by (rewrite Hf, HFRSx; left; reflexivity);
              destruct (al_frames _ _ Lx _ _ _ _ _ 1 ps (proj1 J2) Hin2) as (_ & _ & Hp & _);
              let EF2 := fresh "EF2" in
              destruct (oc_fa_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ J1 J2) as (EF2 & _);
              let a0 := fresh "a0" in let Ha0 := fresh "Ha0" in
              intros a0 Ha0; apply (proj1 (Hp a0 ltac:(rewrite EF2, EFAx, <- HFx; change (fs_frame_bytes 1) with 128; lia)))
              end end
            | match goal with |- ?g => idtac "KF-PRES" g; fail end ] ] end
  end end.

(* the boundary's environment facts (oc_env) for the current environment, from the carried facts *)
Ltac oc_env_tac :=
  lazymatch goal with |- oc_env _ ?Ej =>
  unfold oc_env, oc_sp1, oc_F, oc_FL; cbn [o_regs o_lyc o_pos];
  lazymatch goal with HFx : ?Fv = frame_addr _ 1 _, HFLx : ?FLv = flag_addr _ 1 _ |- _ => rewrite <- HFx, <- HFLx end;
  split;
  [ repeat match goal with
    | |- env_agree 32 _ (havoc _ _ _) => apply env_agree_havoc_ge; [cbv; lia | ]
    | |- env_agree 32 _ (ewset _ _ _) => apply oc_agree_ewset; [ | cbv; lia]
    | |- env_agree 32 _ _ => assumption
    end
  | repeat (first [rewrite oc_ew_out by (cbn [length]; lia) | rewrite ew_ewset_other by lia]);
    repeat split; first [assumption | match goal with |- ?g => idtac "ENV-FAIL" g; fail end] ] end.
(* the carried state (oc_st) at the current journal *)
Ltac oc_st_tac :=
  unfold oc_st; cbn [o_STK o_sp0 o_FP o_ly o_S o_W0 o_mem0 o_md0 o_own o_lyc o_Sc o_W o_memc o_mdc o_k o_regs o_pos oc_E];
  split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|];
  split; [cw_io | eassumption].

(* the shadow table of the frame's two arrays (and of the text byte, tx), from the zero shadow bytes in the frame's
   shadow region of the current state *)
Ltac oc_frame_shok tx :=
  try match goal with Hs : sh_ok _ _ _ _ _ |- _ => clear Hs end;
  lazymatch goal with HS : st_ok _ ?Ev ?ssv (restrict (w_H ?Wc) ?msx), E88x : ew ?Ev 88 = Z_to_bv 64 (SB + ?Fv / 8),
    E75x : ew ?Ev 75 = Z_to_bv 64 ?Fv, E32x : ew ?Ev 32 = Z_to_bv 64 SB, HF8x : ?Fv mod 8 = 0,
    HFh : in_app ?Fv 128, HFc : ?Fv + 128 <= alloc_ceiling, C1x : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000,
    HF4 : 4096 <= ?Fv |- _ =>
  let idx := eval vm_compute in (oc_find88 (ss_mem ssv)) in
  let HRfs := fresh "HRfs" in let ZS := fresh "ZS" in
  pose proof (st_ok_region_nth Ev ssv (restrict (w_H Wc) msx) idx oc_fs_ro HS eq_refl) as HRfs; cbn [ms_mem restrict] in HRfs;
  assert (ZS : forall od, od = 4 \/ od = 8 \/ od = 9 \/ od = 10 \/ od = 11 ->
    aview tfibsegs (w_H Wc) (ms_mem msx) (SB + Fv / 8 + od) = Some 0);
  [ intros od Hod; unfold oc_fs_ro in HRfs;
    destruct Hod as [-> | [-> | [-> | [-> | ->]]]];
    (match goal with |- context [SB + Fv / 8 + ?o] =>
     let V := fresh "V" in
     pose proof (field_of_region _ _ 88 (SB + Fv / 8) oc_fs_chunks 0 16 0 0 o 1%N (SLit 0) 0 HRfs
      ltac:(rewrite E88x; apply unsigned_lit_small; unfold SB; lia) ltac:(cbn; tauto) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V;
     exact (aview_of_val_mem1 tfibsegs _ _ _ 0 V ltac:(lia)) end)
  | ];
  clear HRfs;
  let SHOK := fresh "SHOK" in
  lazymatch tx with
  | true =>
    lazymatch goal with Tra : range_addressable _ _ ?x 1, Tam1 : amem_range ?x 1, E300 : ew Ev 300 = Z_to_bv 64 ?x |- _ =>
    assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 300 0 1; mkSHE 75 32 (32 + 8); mkSHE 75 64 (64 + 32)] Ev (mrestrict (w_H Wc) (ms_mem msx)));
    [ apply Forall_cons; [apply (cw_shent_ra Wc (ms_mem msx) Ev 300 x 1 Tra Tam1); [lia | lia | lia | rewrite E300; reflexivity | exact E32x]|] | ] end
  | false =>
    assert (SHOK : sh_ok tfibsegs CW_Bx [mkSHE 75 32 (32 + 8); mkSHE 75 64 (64 + 32)] Ev (mrestrict (w_H Wc) (ms_mem msx)));
    [ | ]
  end;
  [ repeat (apply Forall_cons); try apply Forall_nil;
    [ apply (oc_shent_frame Ev Wc (ms_mem msx) Fv 32 8 E75x E32x HF8x eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(clear - HFh C1x; unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, ASAN_CEIL in *; lia) ltac:(lia));
      intros j Hj; change (8 / 8) with 1 in Hj; replace j with 0 by lia; change (32 / 8) with 4; rewrite Z.add_0_r; apply ZS; tauto
    | apply (oc_shent_frame Ev Wc (ms_mem msx) Fv 64 32 E75x E32x HF8x eq_refl eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
        ltac:(clear - HFh C1x; unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kHighMemEnd, kLowMemEnd, ASAN_CEIL in *; lia) ltac:(lia));
      intros j Hj; change (32 / 8) with 4 in Hj; change (64 / 8) with 8;
      replace (SB + Fv / 8 + 8 + j) with (SB + Fv / 8 + (8 + j)) by lia; apply ZS; lia ]
  | clear ZS ] end.

(* the branch condition H on the text byte (atom 350 = c, E350x) as a test on c *)
Ltac oc_c350 H :=
  rewrite ?branch_eq_U, ?branch_ne_U in H;
  lazymatch type of H with context [U ?Ecur (SOff 350 0)] =>
    lazymatch goal with E350x : ew _ 350 = Z_to_bv 64 ?cv, Trx : 0 <= ?cv < 256 |- _ =>
    let Hx := fresh in
    assert (Hx : ew Ecur 350 = Z_to_bv 64 cv) by (rewrite ?ew_ewset_other by lia; exact E350x);
    rewrite (cw_U_atom0 Ecur 350 cv Hx ltac:(lia)) in H; clear Hx end end;
  rewrite ?U_lit in H by lia.

(* owed_seg7's own premises at its entry: a0 = the argument, the argument a byte, the image tables at sp1 *)
Ltac oc_seg7_arg :=
  idtac;
  lazymatch goal with
  | |- getr _ 10 = w64 _ =>
    lazymatch goal with HS : st_ok _ _ _ _ |- _ => let R := fresh "R" in rreg HS (10%bv : bv 5) R; rewrite R end;
    first [ reflexivity | lazymatch goal with E350x : ew ?Ex 350 = Z_to_bv 64 _ |- ew ?Ex 350 = _ => rewrite E350x; reflexivity end ]
  | |- 0 <= _ < 256 => lia
  | |- cimg_rd _ _ _ _ _ _ _ _ _ =>
    lazymatch goal with Hp : oc_pre _ _ _ _, KTx : tcj_kept _ _ _ _ _ _ _ _ _ _ _, Hs : spZ (ms_regs _) = _ |- _ =>
      rewrite Hs; eapply (oc_cimg_kt _ _ _ _ _ _ _ _ _ _ _ Hp KTx); cbn [o_regs];
      unfold T_owed_seg7, T_owed_counter_text, ESTACK; lia end
  end.
(* the call of owed_seg7 at its entry 0x8438c: drop the text byte's region (index 0), then CPgWalkCall's
   cpw_call_reseat_at with the callee's sp = sp1 (atom 70) *)
Ltac oc_seg7_call SPEC sp1v :=
  repeat match goal with Hs : sh_ok _ _ _ _ _ |- _ => clear Hs end;
  lazymatch goal with HS : st_ok _ ?Ex ?ssx ?msx |- _ =>
    let rs := eval vm_compute in (tl (ss_mem ssx)) in
    let HS1 := fresh "HS1" in
    pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS1;
    clear HS; rename HS1 into HS; norm_ss HS end;
  cpw_call_reseat_at SPEC sp1v
    ltac:(unfold spZ at 1; lazymatch goal with R2x : getr _ 2 = ew ?Ex 70, E70x : ew ?Ex 70 = Z_to_bv 64 _ |- _ => rewrite R2x, E70x end;
          apply unsigned_lit_small; lia)
    ltac:(first [oc_seg7_arg | match goal with |- ?g => idtac "ARG-FAIL" g; fail end]) [0; 1; 2; 3; 4; 5]%nat
    ltac:(fun K J1 J2 => first [oc_kept_call K J1 J2 | match goal with |- ?g => idtac "KEPTC-FAIL" g; fail end])
    ltac:(first [intros ? [] | match goal with |- ?g => idtac "E1-FAIL" g; fail end]).
(* a register r pinned to a fresh atom a (window [a, a + 1) free) holding its machine value *)
Ltac oc_pin r a :=
  lazymatch goal with HS : st_ok _ ?Ev ?ssx (restrict (w_H ?Wc) ?msx) |- _ =>
    let HS1 := fresh "HS1" in let Ea := fresh "Ea" in
    pose proof (st_ok_havoc_win tfibsegs a Ev ssx _ [getr (ms_regs msx) r] HS ltac:(vm_compute; reflexivity)) as HS1;
    assert (Ea : ew (havoc Ev a [getr (ms_regs msx) r]) a = getr (ms_regs msx) r)
      by exact (ew_havoc_new Ev a [getr (ms_regs msx) r] 0 (Z_to_bv 64 0) ltac:(cbn; lia));
    clear HS; rename HS1 into HS;
    oc_rebase;
    lazymatch goal with HS2 : st_ok _ ?Ev2 ?ss2 ?ms2 |- _ =>
      let HS3 := fresh "HS3" in
      pose proof (st_ok_pin_rege Ev2 ss2 ms2 r (SOff a 0) HS2 ltac:(discriminate)
        ltac:(rewrite sv_denot_SOff0, Ea; reflexivity)) as HS3;
      clear HS2; rename HS3 into HS; norm_ss HS end
  end.
