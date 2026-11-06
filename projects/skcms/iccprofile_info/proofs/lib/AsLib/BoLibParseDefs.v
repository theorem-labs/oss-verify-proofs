(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase BoLibDefs AsRtSpec AsLibTagsSpec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_post_hook ::= idtac.
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
    let G2 := eval lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in G1 in
    change G2
  end.
Local Ltac ev_simpl_in E H ::= try unfold E in H; lazy [ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals] in H.
(* [comment removed for export] *)
#[local] Ltac AsSymDrive.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac AsSymDrive.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.

#[local] Abbreviation SEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Definition tag_offsets : list Z := [232; 208; 184; 160; 136; 112; 88]%Z.

(* [comment removed for export] *)
Ltac frk HF HFK :=
  intros r Hin; repeat (destruct Hin as [<- | Hin]); try (solve [destruct Hin]);
  (etransitivity; [| apply HFK; cbn [In]; clear; repeat (first [left; reflexivity | right])]);
  first [ fregv HF (19%bv:reg); reflexivity | fregv HF (20%bv:reg); reflexivity
        | fregv HF (21%bv:reg); reflexivity | fregv HF (22%bv:reg); reflexivity
        | fregv HF (23%bv:reg); reflexivity | fregv HF (24%bv:reg); reflexivity
        | fregv HF (25%bv:reg); reflexivity | fregv HF (26%bv:reg); reflexivity
        | fregv HF (27%bv:reg); reflexivity ].

Section Defs.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len fs : Z) (bs : list byte) (ch : chain).

  (* [comment removed for export] *)
  Definition PENV : Prop :=
    let p := bv_unsigned P in let q := bv_unsigned prio in let s := bv_unsigned sp in
    let dd := bv_unsigned data in
    getr regs 1 = ret /\ ret_ok ret /\ getr regs 2 = sp /\ getr regs 4 = Z_to_bv 64 (aa_tp both_abi) /\
    as_data_ok ceil mem data len bs /\ (dd + len <= fs \/ fs + FS_SIZE <= dd)%Z /\
    cell32 SEGS mem q 0 /\ cell32 SEGS mem (q + 4) 1 /\ (q mod 8 = 0)%Z /\ heapish ceil q 8 /\ shz mem q 1 /\
    (fs + FS_FRAMES5 <= q)%Z /\ (q + 8 <= fs + FS_SIZE)%Z /\ (q + 8 <= p \/ p + 976 <= q)%Z /\
    writable SEGS mem p 976 /\ (p mod 64 = 0)%Z /\ heapish ceil p 976 /\ shz mem p 122 /\
    (fs + FS_FRAMES5 <= p)%Z /\ (p + 976 <= fs + FS_SIZE)%Z /\
    as_frame SEGS ceil mem sp PARSE_DB /\ shz mem (s - PARSE_DB) (PARSE_DB / 8) /\
    as_env SEGS ceil both_abi fs ch mem /\ fs_hdr SEGS ceil both_abi fs mem /\ fs_writable SEGS fs mem /\
    (exists h, acellw SEGS mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem.

  Definition BIG : list (word * Z) :=
    [(Z_to_bv 64 (bv_unsigned sp - 2928), 2928%Z); (P, 976%Z);
     (Z_to_bv 64 (fs + 0), 8%Z); (Z_to_bv 64 (fs + 4096), 16384%Z);
     (Z_to_bv 64 (fs + 36864), 1048576%Z); (Z_to_bv 64 (2147450880 + (fs + 36864) / 8), 131072%Z)].

  Lemma BIG_eq : ([(Z_to_bv 64 (bv_unsigned sp - PARSE_DB), PARSE_DB); (P, 976%Z)] ++ fs_mod0 fs) = BIG.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      regs_kept abi_kept regs regs' /\
      fregs_kept abi_fkept (fp_regs (FPState:=FP0)) (fp_regs (FPState:=FPI')) /\
      (frame_mod mem mem' BIG /\ fs_flags0_but fs [] mem' /\ (exists h', acellw SEGS mem' (fs + FS_HINT0) h') /\
       exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z /\
         (r = 1%Z -> parsed_ok SEGS mem' data len bs (bv_unsigned P))).

  (* [comment removed for export] *)
  Definition SAVED (M : word -> option byte) : Prop :=
    let s := bv_unsigned sp in
    cell64 SEGS M (s - 8) (getr regs 1) /\ cell64 SEGS M (s - 16) (getr regs 8) /\
    cell64 SEGS M (s - 24) (getr regs 9) /\ cell64 SEGS M (s - 32) (getr regs 18) /\
    cell64 SEGS M (s - 40) (getr regs 19) /\ cell64 SEGS M (s - 48) (getr regs 20) /\
    cell64 SEGS M (s - 56) (getr regs 21) /\ cell64 SEGS M (s - 64) (getr regs 22) /\
    cell64 SEGS M (s - 72) (getr regs 23) /\ cell64 SEGS M (s - 80) (getr regs 24) /\
    cell64 SEGS M (s - 88) (getr regs 25) /\ cell64 SEGS M (s - 96) (getr regs 26) /\
    cell64 SEGS M (s - 104) (getr regs 27) /\
    cell64 SEGS M (s - 112) (reg_get (fp_regs (FPState:=FP0)) 8) /\
    cell64 SEGS M (s - 120) (reg_get (fp_regs (FPState:=FP0)) 9) /\
    cell64 SEGS M (s - 128) (reg_get (fp_regs (FPState:=FP0)) 18).

  (* [comment removed for export] *)
  Definition COMMON (FPI : FPState) (R : bvmap 5 word) : Prop :=
    (bv_unsigned (getr R 2) = bv_unsigned sp - 384)%Z /\
    getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 21 = P /\ getr R 22 = Z_to_bv 64 SB /\
    (forall r, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
       reg_get (fp_regs (FPState:=FPI)) r = reg_get (fp_regs (FPState:=FP0)) r).

  (* [comment removed for export] *)
  Definition FSOK (M : word -> option byte) : Prop :=
    fs_flags0_but fs [] M /\ (exists h, acellw SEGS M (fs + FS_HINT0) h).

  Lemma SAVED_frame : forall M M' rs,
    SAVED M -> frame_mod M M' rs -> apart (bv_unsigned sp - 128) 128 rs -> (128 <= bv_unsigned sp)%Z -> SAVED M'.
  Proof.
    intros M M' rs HS Hf Hap Hsp. pose proof (u64_range sp).
    unfold SAVED in *. cbv zeta in *.
    repeat match goal with |- _ /\ _ => split end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    (eapply cell64_frame; [exact Hf | eassumption | lia | lia | eapply apart_sub; [exact Hap | lia | lia | lia]]).
  Qed.

  Hypothesis HE : PENV.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma penv_nums :
    let p := bv_unsigned P in let q := bv_unsigned prio in let s := bv_unsigned sp in let dd := bv_unsigned data in
    (appm (fs) FS_SIZE /\ (0 < fs)%Z) /\ (fs + FS_SIZE <= ceil)%Z /\ (fs mod 4096 = 0)%Z /\
    ((AS_STKLO <= ceil)%Z /\ (ceil <= s - 2928)%Z) /\ (s <= 2 ^ 47)%Z /\ (s mod 16 = 0)%Z /\
    (appm (p) 976 /\ (0 < p)%Z) /\ (p + 976 <= ceil)%Z /\ (appm (q) 8 /\ (0 < q)%Z) /\ (q + 8 <= ceil)%Z /\
    (appm (dd) len /\ (0 < dd)%Z) /\ (dd + len <= ceil)%Z /\ (0 <= len < 2 ^ 26)%Z.
  Proof.
    destruct HE as (_ & _ & _ & _ & ((Hlen & _) & [D1 D2] & _ & _) & _ & _ & _ & _ & [Q1 Q2] & _ & _ & _ & _ & _ & _ & [P1 P2] & _ & _ & _ &
                     ([St1 St2] & Sal & _) & _ & _ & (_ & _ & _ & F1 & F2 & F3) & _).
    unfold PARSE_DB in *. cbv zeta. app_facts.
    repeat match goal with |- _ /\ _ => split end; first [assumption | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma penv_quot :
    bv_unsigned P = (8 * (bv_unsigned P / 8))%Z /\ bv_unsigned prio = (8 * (bv_unsigned prio / 8))%Z /\
    (fs + 36864 = 8 * ((fs + 36864) / 8))%Z /\ bv_unsigned data = (8 * (bv_unsigned data / 8))%Z /\
    (bv_unsigned sp = 8 * (bv_unsigned sp / 8))%Z /\ (8 * (len / 8) <= len < 8 * (len / 8) + 8)%Z.
  Proof.
    destruct HE as (_ & _ & _ & _ & (_ & _ & Hdal & _) & _ & _ & _ & Hqal & _ & _ & _ & _ & _ & _ & Hpal & _ & _ & _ & _ & (_ & Hsal & _) & _ & _ & (_ & _ & _ & _ & _ & Hfal) & _).
    split; [apply mod_exact; [lia|]; apply (mod_down _ 8 8); [lia|lia|exact Hpal]|].
    split; [apply mod_exact; [lia|exact Hqal]|].
    split. { apply mod_exact; [lia|]. apply (mod_down _ 8 512); [lia|lia|]. change (8*512)%Z with 4096%Z.
             rewrite <- Zplus_mod_idemp_l, Hfal. reflexivity. }
    split; [apply mod_exact; [lia|]; apply (mod_down _ 8 2); [lia|lia|exact Hdal]|].
    split; [apply mod_exact; [lia|]; apply (mod_down _ 8 2); [lia|lia|exact Hsal]|].
    apply div8_bounds.
  Qed.

  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core3 else first [ solve [clear; el_lia_core3] | el_lia_core3 ].   (* [comment removed for export] *)
  Lemma BIG_safe : Forall (env_safe ceil fs) BIG /\ apart (fs + FS_SSL) 9 BIG /\
    apart (bv_unsigned data) len BIG /\ apart (SB + bv_unsigned data / 8) (len / 8 + 1) BIG /\
    apart (bv_unsigned prio) 8 BIG /\ apart (SB + bv_unsigned prio / 8) 1 BIG /\
    apart (SB + bv_unsigned P / 8) 122 BIG /\ apart (bv_unsigned sp - 128) 128 (tl BIG) /\
    apart (SB + (bv_unsigned sp - 2928) / 8) 366 BIG.
  Proof.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    pose proof penv_nums as NU. cbv zeta in NU. destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
    destruct HE as (_ & _ & _ & _ & (_ & _ & Hdal & _) & Hdar & _ & _ & Hqal & _ & _ & Hq1 & Hq2 & Hqp & _ & Hpal & _ & _ & Hp1 & Hp2 & _).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range prio). pose proof (u64_range data).
    unfold BIG, FS_SIZE, FS_FRAMES5, FS_SSL, env_safe, SB, AS_SB in *. cbn [tl].
    split. { repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd]; unfold FS_SIZE;
             rewrite ?u_small by lia; lia. }
    repeat match goal with |- _ /\ _ => split end; solve_apart.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core3 else first [ solve [clear; el_lia_core3] | el_lia_core3 ].   (* [comment removed for export] *)
  Lemma penv_at : forall M, frame_mod mem M BIG ->
    as_data_ok ceil M data len bs /\ as_env SEGS ceil both_abi fs ch M /\ fs_hdr SEGS ceil both_abi fs M /\ fs_writable SEGS fs M /\
    cell32 SEGS M (bv_unsigned prio) 0 /\ cell32 SEGS M (bv_unsigned prio + 4) 1 /\ shz M (bv_unsigned prio) 1 /\
    writable SEGS M (bv_unsigned P) 976 /\ shz M (bv_unsigned P) 122 /\
    writable SEGS M (bv_unsigned sp - 2928) 2928 /\ shz M (bv_unsigned sp - 2928) 366 /\
    as_sb SEGS as_both M /\ env_ro both_abi M.
  Proof.
    intros M HF. pose proof BIG_safe as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & _ & T9).
    pose proof penv_nums as NU. cbv zeta in NU. destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
    destruct HE as (_ & _ & _ & _ & (Hd0 & Hdh & Hdal & Hshd) & Hdar & C0 & C4 & Hqal & _ & Hshq & _ & _ & _ & WP & Hpal & _ & HshP & _ & _ &
                     (_ & _ & WS) & HshS & Henv & Hhdr & Hfsw & _).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range prio). pose proof (u64_range data).
    unfold FS_SIZE, PARSE_DB in *. change (2928 / 8)%Z with 366%Z in HshS.
    assert (HEV : as_env SEGS ceil both_abi fs ch M) by (eapply as_env_frame; [exact both_abi_low | ceil_lo | fs_app | exact HF | exact T1 | exact Henv]).
    split. { split; [eapply data_ok_frame; [exact HF | exact Hd0 | exact T3]|]. split; [exact Hdh|]. split; [exact Hdal|].
             eapply shdata_frame; [exact HF | exact Hshd | lia | lia | lia | exact T4]. }
    split; [exact HEV|].
    split; [eapply fs_hdr_frame; [exact both_abi_low | ceil_lo | exact HF | exact T1 | exact T2 | exact Hhdr]|].
    split; [eapply fs_writable_frame; [exact HF | exact Hfsw]|].
    split; [eapply cell32_frame; [exact HF | exact C0 | lia | lia | eapply apart_sub; [exact T5|lia|lia|lia]]|].
    split; [eapply cell32_frame; [exact HF | exact C4 | lia | lia | eapply apart_sub; [exact T5|lia|lia|lia]]|].
    split; [eapply shz_frame; [exact HF | exact Hshq | lia | lia | exact T6]|].
    split; [eapply writable_frame; [exact HF | exact WP]|].
    split; [eapply shz_frame; [exact HF | exact HshP | lia | lia | exact T7]|].
    split; [eapply writable_frame; [exact HF | exact WS]|].
    split; [eapply shz_frame; [exact HF | exact HshS | lia | lia | exact T9]|].
    split. { apply (proj2 (as_sb_both SEGS M)). destruct HEV as (HC & _). pose proof (both_cells64 SEGS M HC) as (E1 & E2 & _).
             unfold sbcell, cell64, LibDefs.cell. unfold acell in E1, E2. split; [exact E1 | exact E2]. }
    exact (proj1 (proj2 (proj2 HEV))).
  Qed.
  Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

  (* [comment removed for export] *)
  Definition in_big (b : word) (m : Z) : Prop :=
    exists b' n', In (b', n') BIG /\ (bv_unsigned b' <= bv_unsigned b)%Z /\ (bv_unsigned b + m <= bv_unsigned b' + n')%Z.
  Lemma bincl_of : forall rs, Forall (fun r => in_big (fst r) (snd r)) rs -> regions_incl rs BIG.
  Proof. intros rs H b m Hin. rewrite Forall_forall in H. exact (H (b, m) Hin). Qed.
  Lemma frame_BIG_app : forall M1 M2 l,
    frame_mod mem M1 BIG -> frame_mod M1 M2 l -> regions_incl l BIG -> frame_mod mem M2 BIG.
  Proof.
    intros M1 M2 l HA HB Hl. eapply frame_mod_incl; [| exact (frame_mod_trans _ _ _ _ _ HA HB)].
    intros b m Hin. apply in_app_or in Hin as [Hin|Hin]; [exists b, m; split; [exact Hin| lia] | exact (Hl b m Hin)].
  Qed.
  (* [comment removed for export] *)
  Lemma in_big_stack : forall a m, (bv_unsigned sp - 2928 <= a)%Z -> (0 <= m)%Z -> (a + m <= bv_unsigned sp)%Z -> in_big (Z_to_bv 64 a) m.
  Proof.
    intros a m H1 H2 H3. pose proof penv_nums as NU. cbv zeta in NU. pose proof (u64_range sp).
    exists (Z_to_bv 64 (bv_unsigned sp - 2928)), 2928%Z. split; [cbn; tauto|]. rewrite !u_small by lia. lia.
  Qed.
  Lemma in_big_P : forall a m, (bv_unsigned P <= a)%Z -> (0 <= m)%Z -> (a + m <= bv_unsigned P + 976)%Z -> in_big (Z_to_bv 64 a) m.
  Proof.
    intros a m H1 H2 H3. pose proof penv_nums as NU. cbv zeta in NU. pose proof (u64_range P).
    exists P, 976%Z. split; [cbn; tauto|]. rewrite !u_small by lia. lia.
  Qed.
  Lemma in_big_P' : in_big P 976.
  Proof. exists P, 976%Z. split; [cbn; tauto|]. lia. Qed.
  Lemma in_big_fs : forall b m, In (b, m) (fs_mod0 fs) -> in_big b m.
  Proof. intros b m Hin. exists b, m. split; [rewrite <- BIG_eq; apply in_or_app; right; exact Hin | lia]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma gettag_pre_at : forall Mx (FP : FPState) R (k sig psz tc : Z),
    frame_mod mem Mx BIG ->
    cell64 SEGS Mx (bv_unsigned P) data -> cell32 SEGS Mx (bv_unsigned P + 20) tc -> tags_ok len bs tc psz ->
    getr R 21 = P -> getr R 10 = P -> getr R 11 = Z_to_bv 64 sig -> getr R 12 = Z_to_bv 64 (bv_unsigned sp - 384 + k) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 384) ->
    (0 <= sig < 2 ^ 32)%Z -> In k tag_offsets ->
    gettag_pre_as SEGS as_both ceil data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 384 + k)) FP R Mx.
  Proof.
    intros Mx FP R k sig psz tc Hf C0 C20 Ht R21 R10 R11 R12 R2 Hsig Hk.
    pose proof penv_nums as NU. cbv zeta in NU. destruct NU as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11 & N12 & N13).
    destruct (penv_at Mx Hf) as (HD & HEV & _ & _ & _ & _ & _ & WP & HshP & WS & HshS & Hsb & _).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpal & _).
    pose proof (u64_range sp). pose proof (u64_range P).
    assert (Hk' : (k = 232 \/ k = 208 \/ k = 184 \/ k = 160 \/ k = 136 \/ k = 112 \/ k = 88)%Z) by (cbn in Hk; intuition lia).
    clear Hk.
    unfold gettag_pre_as. cbv zeta. rewrite !u_small by lia.
    split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact Hsig|].
    split; [exact HD|]. split; [exact C0|]. split; [exact C20|]. split; [exact Ht|].
    split; [apply (mod_down _ 8 8); [lia|lia|exact Hpal]|]. split; [unfold heapish; plc|].
    split; [eapply (shz_sub Mx _ _ _ _ HshP); [apply (mod_down _ 8 8); [lia|lia|exact Hpal] | lia | lia | lia]|].
    split. { clear -Hk' N6. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             destruct Hk' as [-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]; lia.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    split; [unfold stackish; lia|].
    split; [eapply writable_sub; [exact WS | lia | lia | lia]|].
    split. { eapply (shz_sub Mx _ _ _ _ HshS); [| lia | lia | lia].
             clear -Hk' N6. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
             destruct Hk' as [-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]; lia.
             Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    split; [exact Hsb|].
    exists (Z_to_bv 64 (bv_unsigned sp - 384)). split; [exact R2|].
    unfold as_frame, stackish. rewrite !u_small by lia.
    split; [| lia]. split; [lia|]. split.
    - apply (mod_down _ 16 1); [lia|lia|]. change (16 * 1)%Z with 16%Z. apply mod_sub_multiple; [lia | exact N6 | reflexivity].
    - eapply writable_sub; [exact WS | lia | lia | lia].
  Qed.

  Lemma gettag_big : forall k, In k tag_offsets ->
    regions_incl [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 384 + k), 24%Z)] BIG.
  Proof.
    intros k Hk. pose proof penv_nums as NU. cbv zeta in NU. pose proof (u64_range sp).
    assert (Hk' : (k = 232 \/ k = 208 \/ k = 184 \/ k = 160 \/ k = 136 \/ k = 112 \/ k = 88)%Z) by (cbn in Hk; intuition lia).
    apply bincl_of. repeat (apply Forall_cons); try apply Forall_nil; cbn [fst snd].
    - rewrite u_small by lia. apply in_big_stack; lia.
    - apply in_big_stack; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma saved_tag : forall Mx My k, In k tag_offsets ->
    SAVED Mx -> frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 384 + k), 24%Z)] ->
    SAVED My.
  Proof.
    intros Mx My k Hk HS Hfr. pose proof penv_nums as NU. cbv zeta in NU. pose proof (u64_range sp).
    assert (Hk' : (k = 232 \/ k = 208 \/ k = 184 \/ k = 160 \/ k = 136 \/ k = 112 \/ k = 88)%Z) by (cbn in Hk; intuition lia).
    eapply SAVED_frame; [exact HS | exact Hfr | | lia]. rewrite u_small by lia. solve_apart.
  Qed.

  (* [comment removed for export] *)
  Lemma parsed_tag : forall Mx My k, In k tag_offsets ->
    parsed_ok SEGS Mx data len bs (bv_unsigned P) ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 384 + k), 24%Z)] ->
    parsed_ok SEGS My data len bs (bv_unsigned P).
  Proof.
    intros Mx My k Hk Hpo Hfr. pose proof penv_nums as NU. cbv zeta in NU. pose proof (u64_range sp). pose proof (u64_range P).
    assert (Hk' : (k = 232 \/ k = 208 \/ k = 184 \/ k = 160 \/ k = 136 \/ k = 112 \/ k = 88)%Z) by (cbn in Hk; intuition lia).
    eapply parsed_ok_frame; [exact Hfr | exact Hpo | lia | lia | | |]; rewrite u_small by lia; solve_apart.
  Qed.

  Lemma cell8_P_tag : forall Mx My k o v, In k tag_offsets -> (0 <= o < 976)%Z ->
    cell8 SEGS Mx (bv_unsigned P + o) v ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 384 + k), 24%Z)] ->
    cell8 SEGS My (bv_unsigned P + o) v.
  Proof.
    intros Mx My k o v Hk Ho Hc Hfr. pose proof penv_nums as NU. cbv zeta in NU. pose proof (u64_range sp). pose proof (u64_range P).
    assert (Hk' : (k = 232 \/ k = 208 \/ k = 184 \/ k = 160 \/ k = 136 \/ k = 112 \/ k = 88)%Z) by (cbn in Hk; intuition lia).
    eapply cell8_frame; [exact Hfr | exact Hc | lia | lia | rewrite u_small by lia; solve_apart].
  Qed.

  Lemma FSOK_tag : forall Mx My k, In k tag_offsets ->
    FSOK Mx ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 384)) - 16), 16%Z); (Z_to_bv 64 (bv_unsigned sp - 384 + k), 24%Z)] ->
    FSOK My.
  Proof.
    intros Mx My k Hk [HF1 [hh HF2]] Hfr. pose proof penv_nums as NU. cbv zeta in NU. pose proof (u64_range sp).
    assert (Hk' : (k = 232 \/ k = 208 \/ k = 184 \/ k = 160 \/ k = 136 \/ k = 112 \/ k = 88)%Z) by (cbn in Hk; intuition lia).
    split.
    - eapply (fs_flags0_but_frame fs [] [] Mx My); [exact Hfr | exact HF1 | lia | unfold FS_SIZE in *; lia |].
      intros i Hi Hni. split; [exact Hni|]. unfold FS_FLAGS0_LEN in Hi. unfold FS_FLAGS0, FS_SIZE in *. rewrite u_small by lia. solve_apart.
    - exists hh. unfold FS_HINT0, FS_SIZE in *. eapply acellw_frame; [exact Hfr | exact HF2 | lia | lia | rewrite u_small by lia; solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Exit.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (v : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis H11 : getr R 11 = Z_to_bv 64 v.   (* [comment removed for export] *)
    Hypothesis Hv : (v = 0 \/ v = 1)%Z.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis HFS : FSOK M.
    Hypothesis Hok : v = 1%Z -> parsed_ok SEGS M data len bs (bv_unsigned P).

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI))
             ++ [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
                 getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26;
                 getr regs 27; reg_get (fp_regs (FPState:=FP0)) 8; reg_get (fp_regs (FPState:=FP0)) 9;
                 reg_get (fp_regs (FPState:=FP0)) 18])) (blobs_ev [bs]).
    (* [comment removed for export] *)

    Definition kn_exit : list kentry :=
      [KRange (EVar 2) 0 (2^47);
       KWord (SA (EVar 2) 376) 8 (EVar 64); KWord (SA (EVar 2) 368) 8 (EVar 65);
       KWord (SA (EVar 2) 360) 8 (EVar 66); KWord (SA (EVar 2) 352) 8 (EVar 67);
       KWord (SA (EVar 2) 344) 8 (EVar 68); KWord (SA (EVar 2) 336) 8 (EVar 69);
       KWord (SA (EVar 2) 328) 8 (EVar 70); KWord (SA (EVar 2) 320) 8 (EVar 71);
       KWord (SA (EVar 2) 312) 8 (EVar 72); KWord (SA (EVar 2) 304) 8 (EVar 73);
       KWord (SA (EVar 2) 296) 8 (EVar 74); KWord (SA (EVar 2) 288) 8 (EVar 75);
       KWord (SA (EVar 2) 280) 8 (EVar 76);
       KWord (SA (EVar 2) 272) 8 (EVar 77); KWord (SA (EVar 2) 264) 8 (EVar 78);
       KWord (SA (EVar 2) 256) 8 (EVar 79)].

    Lemma kn_exit_ok : know_ok SEGS E M kn_exit.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK). pose proof (u64_range sp). pose proof penv_nums as NU. cbv zeta in NU.
      unfold SAVED in HS. cbv zeta in HS.
      destruct HS as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & F8 & F9 & F18).
      unfold cell64, cell in *.
      unfold kn_exit, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil];
      [ apply krange_intro; cbn [edenot]; ev_simpl E; lia | ..];
      (eapply (kword_intro SEGS E M (EVar 2) (getr R 2));
       [ cbn [edenot]; ev_simpl E; reflexivity
       | cbn [edenot]; ev_simpl E; reflexivity
       | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
       | rewrite H2;
         lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => ring_simplify a end;
         first [eassumption
               | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => idtac "KWEXIT" a end ] ]).
    Qed.

    Lemma exit_ok : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82194) M rom) Q.
    Proof.
      destruct HC as (H2 & H3 & H4 & H21 & H22 & HFK). pose proof (u64_range sp) as Rsp.
      pose proof HE as HE'. destruct HE' as (Hra & Hret & Hsp & _).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_exit_ok as HK.
      (* [comment removed for export] *)
      pin_reg HR (11%bv:reg) (ELit v) by (rewrite (HR (11%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E; exact H11).
      destruct HFS as [HF1 HF2].
      destruct Hv as [-> | ->];
        run_fp 40%nat (@nil Z) noscr false;
        fin_ret;
        lazymatch goal with
        | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
          exists FP2, R2, M2;
          split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
          split; [ unfold regs_kept, abi_kept; intros r Hin;
                   repeat (destruct Hin as [<- | Hin]); try (solve [destruct Hin]);
                   [ regv_lin HR (2%bv:reg); rewrite H2, <- (Z_to_bv_bv_unsigned 64 (getr regs 2)), Hsp; f_equal; lia
                   | regv HR (3%bv:reg); exact H3
                   | regv HR (4%bv:reg); exact H4
                   | regv HR (8%bv:reg); reflexivity
                   | regv HR (9%bv:reg); reflexivity
                   | regv HR (18%bv:reg); reflexivity
                   | regv HR (19%bv:reg); reflexivity
                   | regv HR (20%bv:reg); reflexivity
                   | regv HR (21%bv:reg); reflexivity
                   | regv HR (22%bv:reg); reflexivity
                   | regv HR (23%bv:reg); reflexivity
                   | regv HR (24%bv:reg); reflexivity
                   | regv HR (25%bv:reg); reflexivity
                   | regv HR (26%bv:reg); reflexivity
                   | regv HR (27%bv:reg); reflexivity ] |];
          split; [ unfold fregs_kept, abi_fkept; intros r Hin;
                   repeat (destruct Hin as [<- | Hin]); try (solve [destruct Hin]);
                   [ fregv HF (8%bv:reg); reflexivity
                   | fregv HF (9%bv:reg); reflexivity
                   | fregv HF (18%bv:reg); reflexivity
                   | .. ];
                   (etransitivity; [| apply HFK; cbn [In]; clear; repeat (first [left; reflexivity | right])]);
                   first [ fregv HF (19%bv:reg); reflexivity | fregv HF (20%bv:reg); reflexivity
                         | fregv HF (21%bv:reg); reflexivity | fregv HF (22%bv:reg); reflexivity
                         | fregv HF (23%bv:reg); reflexivity | fregv HF (24%bv:reg); reflexivity
                         | fregv HF (25%bv:reg); reflexivity | fregv HF (26%bv:reg); reflexivity
                         | fregv HF (27%bv:reg); reflexivity ] |];
          split; [exact Hf|]; split; [exact HF1|]; split; [exact HF2|];
          eexists; split; [regv HR (10%bv:reg); reflexivity|]; split; [lia | exact Hok]
        end.
    Qed.
  End Exit.

  (* [comment removed for export] *)
  Lemma fail_ok : forall (FPI : FPState) R M,
    COMMON FPI R -> SAVED M -> frame_mod mem M BIG -> FSOK M ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x82190) M rom) Q.
  Proof.
    intros FPI R M HC HS Hf HFS.
    pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H21 & H22 & HFK).
    set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
    assert (HK : know_ok SEGS E M []) by constructor.
    run_fp 1%nat [0x82194%Z] noscr false.
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ _ _) _ => apply (exit_ok I R' M 0) end.
    - split; [regv HR (2%bv:reg); cbn [edenot]; ev_simpl E; exact H2|].
      split; [regv HR (3%bv:reg); exact H3|]. split; [regv HR (4%bv:reg); exact H4|].
      split; [regv HR (21%bv:reg); exact H21|]. split; [regv HR (22%bv:reg); exact H22|].
      frk HF HFK.
    - regv HR (11%bv:reg). reflexivity.
    - left; reflexivity.
    - exact HS.
    - exact Hf.
    - exact HFS.
    - intros; exfalso; lia.
  Qed.
End Defs.
