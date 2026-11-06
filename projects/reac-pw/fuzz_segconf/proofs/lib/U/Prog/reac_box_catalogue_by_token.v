(** reac_box_catalogue_by_token (UBSan build, 0x167a0): proof of [reac_box_catalogue_by_token_contract]
    (U/Prog/reac_box_catalogue_by_token_c.v) from the contracts of strlen (U/Prog/strlen_c.v) and fuzz_catalogue_row
    (U/Prog/fuzz_catalogue_row_c.v). The UBSan code is the plain code with the UBSan addresses (level-3 identical, no
    check): this is lib/Prog/reac_box_catalogue_by_token.v over the UBSan image, the table at SEG_UBSAN's 0x21468.

    Code (the UBSan binary): `beqz a0` (not taken: tok <> 0); a 16-byte frame
    (sd ra 8(sp), sd s0 0(sp)); s0 = a0; `jal strlen` (0x1f5cc); a1 = a0; a0 = s0; ld ra, ld s0; sp += 16;
    `j fuzz_catalogue_row` (0x166f4) at the caller's sp with the caller's ra, so fuzz_catalogue_row's post is the
    function's. strlen reads the string, its NUL and the slack to the next 8-byte boundary (seg_tok_bridge.cstr_cut:
    less than 8 bytes, so below the frame when the string ends at or below lo); the table is outside [lo, sp) (stk
    gives a byte there, seg_rom none, cat_img the image byte), so the frame stores leave it as in the image; the
    answer is cat_ptr of by_token by seg_tok_bridge.row_ptr_by_token. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_tok_bridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import strlen_c fuzz_catalogue_row_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.U.Prog Require Import reac_box_catalogue_by_token_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_box_catalogue_by_token_holds :
  strlen_contract -> fuzz_catalogue_row_contract -> reac_box_catalogue_by_token_contract.
Proof.
  intros HSL HFC. unfold reac_box_catalogue_by_token_contract, REAC_BOX_CATALOGUE_BY_TOKEN.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo s
    (Htok & HC & HAP & (ST & HK & HS16 & HW) & HT & MI).
  unfold BY_TOKEN_STACK in HK. unfold apart in HAP.
  destruct (cstr_cut rsegs m (bv_unsigned a0) s HC) as (bs & sl & HB & Hz & Hnz & Hn & Hlen & Hsl & Hsl8). clear HC.
  pose proof (bytes_at_bound _ _ _ _ HB) as BB. rewrite length_app in BB. cbn [length] in BB.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA. cbn in RA.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* The table lies outside [lo, sp). *)
  assert (TA : forall a, sa_catalogue SEG_UBSAN <= a < sa_catalogue SEG_UBSAN + CAT_BYTES -> a < lo \/ bv_unsigned sp <= a).
  { intros a Ha. destruct (Z.lt_ge_cases a lo) as [L|L]; [left; exact L|].
    destruct (Z.lt_ge_cases a (bv_unsigned sp)) as [G|G]; [|right; exact G]. exfalso.
    destruct ST as (_ & _ & STa). destruct (STa a ltac:(lia)) as [_ (b & Hb)].
    rewrite (HT a Ha), (HW a ltac:(lia)) in Hb. discriminate. }
  (* Keep the entry facts out of the store automation's reach. *)
  pose proof (conj HB HT) as KEEP. clear HB HT.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step. if_false.
  carve_frame 16%nat ST.
  step. step. step. step. step.
  (* strlen's entry 0x1f5cc with ra = 0x167b8; the frame [sp - 16, sp) holds s0 and ra. *)
  destruct KEEP as [HB HT].
  assert (HB1 : bytes_at rsegs m1 (bv_unsigned a0) (bs ++ Z_to_bv 8 0 :: sl)).
  { eapply bytes_at_transport; [exact HB | exact MU |]. rewrite length_app. cbn [length disjoint_from].
    split; [|exact I]. lia. }
  eapply evt_cut.
  { eapply HSL with (str := bs) (slack := sl); [exact HB1 | exact Hn | exact Hsl | exact MI]. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> &
              MU2 & WM2 & MI2 & HB2).
  rewrite ret_pc_even by (try lia; reflexivity).
  pose proof (rw_cells_transport rsegs [] m1 m2 _ _ FR MU2 WM2 I) as FR2.
  pose proof (stk_transport_disjoint rsegs [] m1 m2 _ _ ST MU2 WM2 I) as ST2.
  assert (MU2' : munch [(bv_unsigned sp + -16, bv_unsigned sp)] m m2).
  { eapply munch_trans; [exact MU | eapply munch_weaken; [|exact MU2]]. intros x _. exact I. }
  pose proof (wmono_trans rsegs _ _ _ WM WM2) as WM2'.
  clear FR ST MU WM MU2 WM2 MI HB1.
  (* 0x167b8: a1 = n, a0 = token, ra and s0 restored, sp back, `j fuzz_catalogue_row`. *)
  step. step. step. step. step. step.
  release_frame FR2 ST2 (bv_unsigned sp).
  apply bytes_at_app in HB2. destruct HB2 as [HS2 _].
  assert (HT2 : forall a, FUZZ_CATALOGUE <= a < FUZZ_CATALOGUE + CAT_BYTES -> mrd rsegs m2 (wa a) = seg_rom rsegs (wa a)).
  { intros a Ha. pose proof (TA a Ha) as Ta. unfold mrd. rewrite (MU2' (wa a)); [exact (HT a Ha)|].
    unfold FUZZ_CATALOGUE, CAT_BYTES in Ha. cbn [outside]. rewrite wa_unsigned by lia. split; [lia | exact I]. }
  eapply evt_cut.
  { eapply HFC with (sb := bs) (lo := lo); rewrite ?unsigned_lit by lia.
    - exact HS2.
    - reflexivity.
    - exact ST2.
    - unfold FCR_STACK. lia.
    - exact HW.
    - lia.
    - exact HT2.
    - exact MI2. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              -> & MU3 & WM3 & MI3 & ST3).
  apply evt_done. unfold ret_post. cbv beta.
  exists t0'', t1'', t2'', a1'', a2'', a3'', a4'', a5'', a6'', a7'', t3'', t4'', t5'', t6'', m3.
  split; [rewrite (row_ptr_by_token FUZZ_CATALOGUE bs) by (rewrite Hz; exact Hnz); rewrite Hz; reflexivity|].
  split.
  { eapply munch_trans; [eapply munch_weaken; [|exact MU2'] | exact MU3].
    unfold sub_fp, BY_TOKEN_STACK. cbn [outside]. intros x [Hx _]. split; [lia | exact I]. }
  split; [exact (wmono_trans rsegs _ _ _ WM2' WM3)|].
  split; [exact MI3|]. split; [exact ST3|]. exact I.
Qed.
