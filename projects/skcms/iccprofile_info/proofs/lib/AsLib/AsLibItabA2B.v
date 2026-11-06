(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.skcms.iccprofile_info.lib.H Require GcFlushY33.  (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsLibWP2Spec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac ev_simpl E ::=
  lazymatch goal with |- ?G =>
    let G1 := match tt with | _ => eval unfold E in G | _ => G end in
    let G2 := eval lazy [ev eb vals_ev blobs_ev app junk_vals fjunk_vals] in G1 in
    let G3 := eval cbn [nth] in G2 in
    change G3
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev app junk_vals fjunk_vals] in H; cbn [nth] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
#[local] Abbreviation SEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
Definition kn_it (c : nat) : list kentry :=
  [KWord (SA (EVar 15) 144) 4 (ELit (Z.of_nat c)); KWord (SA (EVar 15) 300) 4 (ELit 3)]
  ++ firstn c [KWord (SA (EVar 15) 148) 1 (EVar 64); KWord (SA (EVar 15) 149) 1 (EVar 65);
              KWord (SA (EVar 15) 150) 1 (EVar 66); KWord (SA (EVar 15) 151) 1 (EVar 67)]
  ++ firstn c [KRange (EVar 64) 2 255; KRange (EVar 65) 2 255; KRange (EVar 66) 2 255; KRange (EVar 67) 2 255]
  ++ [KRange (EVar 13) 2 4096; KRange (EVar 14) 2 4096; KRange (EVar 11) 0 67108864;
      KRange (EVar 10) 1 (2 ^ 47 - 16); KRange (EVar 15) 1 (2 ^ 47 - 400); KAlign (EVar 15) 8;
      KWr (SA (EVar 15) 0) 400; KRange (EVar 2) (AS_STKLO + 112) (2^47); KWr (SA (EVar 2) (-112)) 112; KDisj (SA (EVar 2) (-112)) 112 (SA (EVar 15) 0) 400;
      KWord (SA (ELit 0) 0x9eaf0) 8 (ELit 0xa6bb8); KWord (SA (ELit 0) 0xa6bb8) 8 (ELit SB);
      KZero (SA (EAlu ALU_SRL (EVar 15) (ELit 3)) SB) (ELit 50);
      KDisj (SA (EVar 15) 0) 400 ZSH ZSHL; KDisj (SA (EVar 15) 0) 400 ZIMG ZIMGL].

Section P.
  Variable ceil : Z.
  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp tb A : word) (maxlen bw ite ote ic : Z) (gps : list Z).
  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : itab_a2b_pre_as SEGS as_asan ceil data len bs sp tb A maxlen bw ite ote ic gps FPI regs mem.

  #[local] Abbreviation g0 := (nth 0 gps 0%Z).
  #[local] Abbreviation g1 := (nth 1 gps 0%Z).
  #[local] Abbreviation g2 := (nth 2 gps 0%Z).
  #[local] Abbreviation g3 := (nth 3 gps 0%Z).

  Let E : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FPI))
                                ++ [Z_to_bv 64 g0; Z_to_bv 64 g1; Z_to_bv 64 g2; Z_to_bv 64 g3; data; Z_to_bv 64 len])) (blobs_ev [bs]).

  Lemma kn_it_ok : forall c : nat, Z.of_nat c = ic -> know_ok SEGS E mem (kn_it c).
  Proof using ceil FPI regs mem data len bs sp tb A maxlen bw ite ote ic gps HPRE.
    intros c Hc.
    destruct HPRE as (Hsp & Htb & Hml & Hbw & Hite & Hote & HA & (Hdok & Hdheap & Hdal & Hshd) & Hml0 & Hin & Hbw12 & Hiter & Hoter &
                      Hic & Hlen_g & Hgps & Cic & Coc & Cg & WA & HalA & HAheap & HshA & D2 & Hsb & (Hstk & Hspal & Wsp)).
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob). destruct Hin as (Hin1 & _ & Hin2).
    destruct WA as (WA1 & WA2 & WA3 & WA4). destruct Wsp as (WS1 & WS2 & WS3 & WS4).
    apply (as_sb_asan SEGS mem) in Hsb. destruct Hsb as [Hg1 Hg2]. unfold cell64, cell in Hg1, Hg2.
    unfold ITAB_FR, heapish, stackish in *. app_facts.
    pose proof (u64_range tb). pose proof (u64_range A). pose proof (u64_range data). pose proof (u64_range sp).
    assert (Gr : forall i, (0 <= i < ic)%Z -> (2 <= nth (Z.to_nat i) gps 0 <= 255)%Z).
    { intros i Hi. apply (Forall_nth (fun g => (2 <= g <= 255)%Z) gps); [exact Hgps|]. lia. }
    assert (Gc : forall (i : Z) (v : expr) (off : Z), (0 <= i < ic)%Z -> off = (148 + i)%Z ->
              edenot E v = Z_to_bv 64 (nth (Z.to_nat i) gps 0%Z) ->
              kentry_ok SEGS E mem (KWord (SA (EVar 15) off) 1 v)).
    { intros i v off Hi -> Hv. pose proof (Cg i Hi) as [Gi Ci].
      eapply (kword_intro SEGS E mem (EVar 15) A (148 + i) 1 v (Z_to_bv 64 (nth (Z.to_nat i) gps 0%Z)));
        [cbn [edenot]; ev_simpl E; exact HA | exact Hv | lia | lia | lia | lia | ].
      replace (bv_unsigned A + (148 + i))%Z with (bv_unsigned A + 148 + i)%Z by lia. exact Ci. }
    assert (Gk : forall (i : Z) (v : expr), (0 <= i < ic)%Z ->
              edenot E v = Z_to_bv 64 (nth (Z.to_nat i) gps 0%Z) ->
              kentry_ok SEGS E mem (KRange v 2 255)).
    { intros i v Hi Hv. apply krange_intro. pose proof (Gr i Hi) as Gi. rewrite Hv, u_small by lia. lia. }
    assert (V0 : edenot E (EVar 64) = Z_to_bv 64 (nth (Z.to_nat 0) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (V1 : edenot E (EVar 65) = Z_to_bv 64 (nth (Z.to_nat 1) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (V2 : edenot E (EVar 66) = Z_to_bv 64 (nth (Z.to_nat 2) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (V3 : edenot E (EVar 67) = Z_to_bv 64 (nth (Z.to_nat 3) gps 0%Z)) by (cbn [edenot]; ev_simpl E; reflexivity).
    assert (c = 1 \/ c = 2 \/ c = 3 \/ c = 4)%nat as Hc4 by lia.
    unfold kn_it.
    apply know_ok_app.
    { constructor; [|constructor; [|constructor]].
      - eapply (kword_intro SEGS E mem (EVar 15) A 144 4 (ELit (Z.of_nat c)) (Z_to_bv 64 ic));
          [cbn [edenot]; ev_simpl E; exact HA | rewrite Hc; reflexivity | lia | lia | lia | lia | exact (proj2 Cic)].
      - eapply (kword_intro SEGS E mem (EVar 15) A 300 4 (ELit 3) (Z_to_bv 64 3));
          [cbn [edenot]; ev_simpl E; exact HA | reflexivity | lia | lia | lia | lia | exact (proj2 Coc)]. }
    apply know_ok_app.
    { destruct Hc4 as [-> |[-> |[-> | ->]]]; cbn [firstn];
      repeat (apply Forall_cons); try apply Forall_nil;
      first [ exact (Gc 0%Z (EVar 64) 148%Z ltac:(lia) eq_refl V0) | exact (Gc 1%Z (EVar 65) 149%Z ltac:(lia) eq_refl V1)
            | exact (Gc 2%Z (EVar 66) 150%Z ltac:(lia) eq_refl V2) | exact (Gc 3%Z (EVar 67) 151%Z ltac:(lia) eq_refl V3) ]. }
    apply know_ok_app.
    { destruct Hc4 as [-> |[-> |[-> | ->]]]; cbn [firstn];
      repeat (apply Forall_cons); try apply Forall_nil;
      first [ exact (Gk 0%Z (EVar 64) ltac:(lia) V0) | exact (Gk 1%Z (EVar 65) ltac:(lia) V1)
            | exact (Gk 2%Z (EVar 66) ltac:(lia) V2) | exact (Gk 3%Z (EVar 67) ltac:(lia) V3) ]. }
    repeat (apply Forall_cons); try apply Forall_nil.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hite, u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hote, u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hml, u_small by lia; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Htb; lia.
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite HA; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite HA. exact HalA.
    - apply (kwr_intro SEGS E mem (EVar 15) A 0 400); [cbn [edenot]; ev_simpl E; exact HA | lia | lia | lia | exact WA4].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; lia.
    - apply (kwr_intro SEGS E mem (EVar 2) sp (-112) 112); [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia | ].
      replace (bv_unsigned sp + -112)%Z with (bv_unsigned sp - 112)%Z by lia. exact WS4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite Hsp, HA. lia.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0x9eaf0 8 (ELit 0xa6bb8) (Z_to_bv 64 0xa6bb8)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kword_intro SEGS E mem (ELit 0) (Z_to_bv 64 0) 0xa6bb8 8 (ELit SB) (Z_to_bv 64 SB)); cbn; rewrite ?u_lit0; cbn; try lia; auto.
    - eapply (kzero_shz_intro SEGS E mem (EVar 15) A 50); [cbn [edenot]; ev_simpl E; exact HA | exact HshA | lia | lia].
    - kdisj_place.
    - kdisj_place.
  Qed.

  Definition Qpost : machine_state -> Prop := fun st' : machine_state =>
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      (regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
       itab_a2b_post_as SEGS data len bs sp tb A maxlen bw ite ote ic gps regs mem FPI' regs' mem').

  (* [comment removed for export] *)
  Ltac clear_junk :=
    repeat match goal with H : (_ <= _)%Z \/ (_ <= _)%Z |- _ => clear H end;
    repeat match goal with H : forall i : Z, _ -> mem _ = _ |- _ => clear H end;
    repeat match goal with H : forall i : Z, _ -> cell8 _ _ _ _ |- _ => clear H end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac mods_in H :=
    repeat match type of H with context [ (?a mod ?b)%Z ] =>
      lazymatch a with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small a b) in H by lia end end.
  Ltac mods_goal :=
    repeat match goal with |- context [ (?a mod ?b)%Z ] =>
      lazymatch a with context [ (_ mod _)%Z ] => fail | _ => rewrite (Z.mod_small a b) by lia end end.
  Ltac wz_in H :=
    rewrite ?u_add64, ?u_mul64 in H; rewrite_getr_in H; rewrite ?u_lit64a in H; mods_in H.
  Ltac wz_goal :=
    rewrite ?u_add64, ?u_mul64; rewrite_getr; rewrite ?u_lit64a; mods_goal.

  Ltac kept_tac :=
    lazymatch goal with
    | HR : regs_ok ?E _ ?R, HF : fregs_ok _ _ (@fp_regs ?I), HR0 : id (regs_ok _ ?sr0 ?regs), HF0 : id (fregs_ok _ ?sfr0 ?fr) |- _ =>
      split; [exact (regs_same_on E sr0 _ regs R abi_kept HR0 HR ltac:(vm_compute; reflexivity))|];
      split; [exact (fregs_same_on E sfr0 _ fr _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity))|]
    end.

  Ltac regions_eq :=
    cbn [regions_denot map fst snd]; unfold adenot, v_addi; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr;
    repeat (apply f_equal2; [apply f_equal2; [apply f_equal; lia | lia] | ]); reflexivity.

  (* [comment removed for export] *)
  Ltac frame_logs RS :=
    lazymatch goal with
    | |- frame_mod ?m0 ?m0 _ => apply frame_mod_refl
    | |- frame_mod ?m0 (mem_denot _ ?m1 ?log) _ =>
        apply (frame_mod_trans_same m0 m1);
        [ frame_logs RS
        | apply (frame_mod_mem_denot E m1 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia
          | vm_compute; reflexivity ] ]
    end.
  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?Mx _ |- _ => is_var Mx; subst Mx end.
  Ltac frame_of_log E RS :=
    subst_mems;
    lazymatch goal with
    | |- frame_mod _ _ ?regions => replace regions with (regions_denot E RS) by regions_eq; frame_logs RS
    end.

  Ltac flat_tac := unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E; rewrite_getr; lia.

  (* [comment removed for export] *)
  Ltac kcellv b k n H :=
    lazymatch goal with HK : know_ok _ ?E ?M ?kn |- _ =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with
      | Some ?v =>
        let KR := fresh "KR" in let Hfl := fresh "Hfl" in
        assert (KR : kread SEGS kn b k n = Some v) by (vm_compute; reflexivity);
        pose proof (kread_rdn SEGS E M kn b k n v HK KR ltac:(lia) ltac:(lia)) as H; clear KR;
        lazymatch type of H with ?FL -> _ => assert (Hfl : FL) by flat_tac; specialize (H Hfl); clear Hfl end;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E H; rewrite_getr_in H;
        rewrite ?ext_val_zx_id4 in H by (rewrite ?u_small by lia; lia);
        rewrite ?ext_val_zx_id1 in H by (rewrite ?u_small by lia; lia)
      | _ => fail "kcellv: no knowledge at" b k n
      end
    end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac wval t U :=
    eassert (U : bv_unsigned t = _)
      by (rewrite ?u_add64, ?u_mul64; rewrite_getr; rewrite ?u_lit64a; mods_goal; reflexivity).

  (* [comment removed for export] *)
  Ltac curve_at off :=
    let C1 := fresh "C" in let C2 := fresh "C" in let C3 := fresh "C" in
    let U8 := fresh "U" in let U16 := fresh "U" in
    let o8 := eval vm_compute in (off + 8)%Z in let o16 := eval vm_compute in (off + 16)%Z in
    kcellv (EVar 15) off 4%nat C1; kcellv (EVar 15) o8 8%nat C2; kcellv (EVar 15) o16 8%nat C3;
    lazymatch type of C1 with _ = Some (word_to_le_bytes 4 (Z_to_bv 64 ?n)) =>
    lazymatch type of C2 with _ = Some (word_to_le_bytes 8 ?t8) =>
    lazymatch type of C3 with _ = Some (word_to_le_bytes 8 ?t16) =>
      wval t8 U8; wval t16 U16;
      exists n, t8, t16;
      split; [split; [lia | exact C1]|];
      split; [replace (bv_unsigned A + off + 8)%Z with (bv_unsigned A + o8)%Z by lia; exact C2|];
      split; [replace (bv_unsigned A + off + 16)%Z with (bv_unsigned A + o16)%Z by lia; exact C3|];
      right; unfold inDATA; rewrite ?U8, ?U16; lia
    end end end.

  Ltac curves_in :=
    intros i Hi;
    let Hi4 := fresh "Hi4" in
    assert (Hi4 : (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%Z) by lia;
    destruct Hi4 as [-> |[-> |[-> | ->]]];
    [ replace (bv_unsigned A + 32 * 0)%Z with (bv_unsigned A + 0)%Z by lia; curve_at 0%Z
    | first [exfalso; lia | replace (bv_unsigned A + 32 * 1)%Z with (bv_unsigned A + 32)%Z by lia; curve_at 32%Z]
    | first [exfalso; lia | replace (bv_unsigned A + 32 * 2)%Z with (bv_unsigned A + 64)%Z by lia; curve_at 64%Z]
    | first [exfalso; lia | replace (bv_unsigned A + 32 * 3)%Z with (bv_unsigned A + 96)%Z by lia; curve_at 96%Z] ].

  Ltac curves_out :=
    intros i Hi;
    let Hi3 := fresh "Hi3" in
    assert (Hi3 : (i = 0 \/ i = 1 \/ i = 2)%Z) by lia;
    destruct Hi3 as [-> |[-> | ->]];
    [ replace (bv_unsigned A + 304 + 32 * 0)%Z with (bv_unsigned A + 304)%Z by lia; curve_at 304%Z
    | replace (bv_unsigned A + 304 + 32 * 1)%Z with (bv_unsigned A + 336)%Z by lia; curve_at 336%Z
    | replace (bv_unsigned A + 304 + 32 * 2)%Z with (bv_unsigned A + 368)%Z by lia; curve_at 368%Z ].

  Ltac grid_tac :=
    let C1 := fresh "C" in let C2 := fresh "C" in let U8 := fresh "U" in let U16 := fresh "U" in
    kcellv (EVar 15) 128%Z 8%nat C1; kcellv (EVar 15) 136%Z 8%nat C2;
    lazymatch type of C1 with _ = Some (word_to_le_bytes 8 ?g8) =>
    lazymatch type of C2 with _ = Some (word_to_le_bytes 8 ?g16) =>
      wval g8 U8; wval g16 U16;
      exists g8, g16; split; [exact C1|]; split; [exact C2|];
      lazymatch goal with Hz : zprod gps = _ |- _ => rewrite Hz end;
      unfold inDATA; rewrite ?U8, ?U16; split; (intros Hbw'; try (exfalso; lia); split; lia)
    end end.

  Ltac prelim :=
    pose proof HPRE as (Hsp & Htb & Hml & Hbw & Hite & Hote & HA & (Hdok & Hdheap & Hdal & Hshd) & Hml0 & Hin & Hbw12 & Hiter & Hoter &
                      Hic & Hlen_g & Hgps & Cic & Coc & Cg & WA & HalA & HAheap & HshA & D2 & Hsb & (Hstk & Hspal & Wsp));
    pose proof Hdok as (Hlen & Hbs & Hdnz & Hdhi & Hblob); destruct Hin as (Hin1 & _ & Hin2);
    destruct WA as (WA1 & WA2 & WA3 & WA4); destruct Wsp as (WS1 & WS2 & WS3 & WS4);
    unfold ITAB_FR, heapish, stackish in Hdheap, HAheap, Hstk; app_facts;
    pose proof (u64_range tb); pose proof (u64_range A); pose proof (u64_range data); pose proof (u64_range sp);
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs]));
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs]));
    (* [comment removed for export] *)
    assert (HR : regs_ok E (sr_upd (sr_vars 0) 12 (ELit bw)) regs) by
      (apply (regs_ok_pin E _ regs 12); [exact HR0|]; cbn [edenot]; exact Hbw);
    pose proof (HR0 : id _) as HRid; clear HR0; pose proof (HF : id _) as HFid;
    clear HalA;
    assert (Uite : bv_unsigned (Z_to_bv 64 ite) = ite) by (apply u_small; lia);
    assert (Uote : bv_unsigned (Z_to_bv 64 ote) = ote) by (apply u_small; lia);
    assert (Uml : bv_unsigned (Z_to_bv 64 maxlen) = maxlen) by (apply u_small; lia);
    clear_junk;
    (* [comment removed for export] *)
    assert (Gr : forall i, (0 <= i < ic)%Z -> (2 <= nth (Z.to_nat i) gps 0 <= 255)%Z) by
      (intros i Hi; apply (Forall_nth (fun g => (2 <= g <= 255)%Z) gps); [exact Hgps|]; lia).

  (* [comment removed for export] *)
  Ltac usmall :=
    repeat match goal with U : bv_unsigned (Z_to_bv 64 ?z) = ?z |- context [bv_unsigned (Z_to_bv 64 ?y)] => constr_eq z y; rewrite !U end.

  (* [comment removed for export] *)
  Ltac sc_tac := rewrite ?u_add64, ?u_mul64; rewrite_getr; rewrite ?u_lit64a; usmall; mods_goal; mod2_split; lia.

  Lemma sltu_xori1 : forall a b : word,
    alu64 ALU_XOR (alu64 ALU_SLTU a b) (Z_to_bv 64 1) = Z_to_bv 64 (if (bv_unsigned a <? bv_unsigned b)%Z then 0 else 1).
  Proof using .
    intros a b. rewrite alu_xor, alu_sltu. unfold v_xor, v_sltu, c_ltu, bv_ltu.
    destruct (bv_unsigned a <? bv_unsigned b)%Z; rewrite ?u_lit64a; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac run_case c :=
    pose proof (kn_it_ok c ltac:(lia)) as HK; cbv beta delta [kn_it firstn app Z.of_nat Pos.of_succ_nat Pos.succ] in HK;
    run_fp 300%nat (@nil Z) noscr true;
    let Hbr := fresh "Hbr" in
    branch_case as Hbr; br_simpl_in E Hbr; run_fp 300%nat (@nil Z) noscr true.

  (* [comment removed for export] *)
  Ltac finish_as :=
    fin_ret;
    lazymatch goal with |- Qpost (@mkst ?I ?R' _ ?M' _) =>
      exists I, R', M';
      split; [ lazymatch goal with HR : regs_ok _ _ R' |- _ => regv HR (1%bv:reg) end; rewrite_getr; reflexivity |];
      kept_tac;
      unfold itab_a2b_post_as, ITAB_FR; cbv zeta;
      exists (bv_unsigned (getr R' 10)); split; [symmetry; apply Z_to_bv_bv_unsigned|];
      lazymatch goal with HR : regs_ok _ _ R' |- _ => regv HR (10%bv:reg) end;
      rewrite sltu_xori1;
      lazymatch goal with Hbr : (_ <? _)%Z = _ |- _ => rewrite Hbr; rewrite u_small by lia; wz_in Hbr end
    end.

  Ltac fin0 := finish_as; left; split; [lia|]; frame_of_log E [(SA (EVar 2) (-112), 112%Z)].

  Ltac fin1 c :=
    finish_as; right; split; [lia|];
    clear_junk;
    let n := eval vm_compute in (32 * Z.of_nat c)%Z in
    split; [frame_of_log E [(SA (EVar 2) (-112), 112%Z); (SA (EVar 15) 0, n); (SA (EVar 15) 128, 16%Z); (SA (EVar 15) 304, 96%Z)]|];
    split; [curves_in|];
    split; [curves_out|];
    grid_tac.

  Ltac fin_case :=
    lazymatch goal with
    | Hbr : (_ <? _)%Z = true |- _ => fin0
    | Hc : ic = 1%Z |- _ => fin1 1%nat
    | Hc : ic = 2%Z |- _ => fin1 2%nat
    | Hc : ic = 3%Z |- _ => fin1 3%nat
    | Hc : ic = 4%Z |- _ => fin1 4%nat
    end.

  Theorem body : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x87208) mem rom) Qpost.
  Proof using ceil FPI regs mem rom ret data len bs sp tb A maxlen bw ite ote ic gps Hra Hret HPRE.
    prelim.
    assert (Hc4 : (ic = 1 \/ ic = 2 \/ ic = 3 \/ ic = 4)%Z) by lia.
    destruct Hc4 as [Hc|[Hc|[Hc|Hc]]];
      [ assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        pose proof (zprod_len1 gps ltac:(lia)) as Hz
      | assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        assert (Gr1 : (2 <= g1 <= 255)%Z) by (apply (Gr 1%Z); lia);
        pose proof (mul_bnd g0 g1 255%Z 255%Z ltac:(lia) ltac:(lia)) as GB01;
        pose proof (zprod_len2 gps ltac:(lia)) as Hz
      | assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        assert (Gr1 : (2 <= g1 <= 255)%Z) by (apply (Gr 1%Z); lia);
        assert (Gr2 : (2 <= g2 <= 255)%Z) by (apply (Gr 2%Z); lia);
        pose proof (mul_bnd g0 g1 255%Z 255%Z ltac:(lia) ltac:(lia)) as GB01;
        pose proof (mul_bnd (g0 * g1) g2 (255 * 255)%Z 255%Z ltac:(lia) ltac:(lia)) as GB012;
        pose proof (zprod_len3 gps ltac:(lia)) as Hz
      | assert (Gr0 : (2 <= g0 <= 255)%Z) by (apply (Gr 0%Z); lia);
        assert (Gr1 : (2 <= g1 <= 255)%Z) by (apply (Gr 1%Z); lia);
        assert (Gr2 : (2 <= g2 <= 255)%Z) by (apply (Gr 2%Z); lia);
        assert (Gr3 : (2 <= g3 <= 255)%Z) by (apply (Gr 3%Z); lia);
        pose proof (mul_bnd g0 g1 255%Z 255%Z ltac:(lia) ltac:(lia)) as GB01;
        pose proof (mul_bnd (g0 * g1) g2 (255 * 255)%Z 255%Z ltac:(lia) ltac:(lia)) as GB012;
        pose proof (mul_bnd (g0 * g1 * g2) g3 (255 * 255 * 255)%Z 255%Z ltac:(lia) ltac:(lia)) as GB0123;
        pose proof (zprod_len4 gps ltac:(lia)) as Hz ].
    all: destruct Hbw12 as [Hbw1 | Hbw2]; [rewrite Hbw1 in HR | rewrite Hbw2 in HR].
    - run_case 1%nat. + fin_case. + fin_case.
    - run_case 1%nat. + fin_case. + fin_case.
    - run_case 2%nat. + fin_case. + fin_case.
    - run_case 2%nat. + fin_case. + fin_case.
    - run_case 3%nat. + fin_case. + fin_case.
    - run_case 3%nat. + fin_case. + fin_case.
    - run_case 4%nat. + fin_case. + fin_case.
    - run_case 4%nat. + fin_case. + fin_case.
  Qed.
End P.

Theorem init_tables_a2b_as_ok : forall ceil, init_tables_a2b_contract_as SEGS as_asan ceil.
Proof.
  intros ceil data len bs sp tb A maxlen bw ite ote ic gps FPI regs mem rom ret Hra Hret HPRE.
  exact (runs_to_contract SEGS _ ret rom _ (body ceil FPI regs mem rom ret data len bs sp tb A maxlen bw ite ote ic gps Hra Hret HPRE)).
Qed.
