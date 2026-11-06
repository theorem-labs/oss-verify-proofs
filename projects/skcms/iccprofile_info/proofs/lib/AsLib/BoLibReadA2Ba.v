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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibWP2Spec LibWP2Lib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs BoBase AsRtSpec AsLibFrame AsLibEnv AsLibTagsLib AsLibFPSpec AsLibWP2Spec BoLibSpec AsLibPlace.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymDriveLZ.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
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
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rs_within (rs RS : list (word * Z)) : Prop :=
  Forall (fun r => (0 <= snd r)%Z /\
                   Exists (fun R => (bv_unsigned (fst R) <= bv_unsigned (fst r))%Z /\
                                     (bv_unsigned (fst r) + snd r <= bv_unsigned (fst R) + snd R)%Z) RS) rs.

Lemma within_outside1 : forall (b : word) (n : Z) RS x,
  Exists (fun R => (bv_unsigned (fst R) <= bv_unsigned b)%Z /\
                   (bv_unsigned b + n <= bv_unsigned (fst R) + snd R)%Z) RS ->
  outside x RS -> ~ in_rng x b n.
Proof.
  intros b n RS x H. induction H as [[B N] RS' HB | [B N] RS' HB IH].
  - cbn [outside fst snd] in *. intros [H1 _]. unfold in_rng in *. lia.
  - cbn [outside]. intros [_ H2]. apply IH. exact H2.
Qed.

Lemma within_outside : forall rs RS x, rs_within rs RS -> outside x RS -> outside x rs.
Proof.
  intros rs RS x H Hout. induction H as [|[b n] rs [_ Hb] Hrs IH]; cbn [outside]; [exact I|].
  split; [| exact IH]. eapply within_outside1; [exact Hb | exact Hout].
Qed.

Lemma frame_mod_within : forall m m' rs RS, rs_within rs RS -> frame_mod m m' rs -> frame_mod m m' RS.
Proof.
  intros m m' rs RS Hw Hf. eapply frame_mod_weaken; [| exact Hf]. intros a Ha. eapply within_outside; eauto.
Qed.

Lemma apart_within1 : forall (b : word) (m : Z) RS lo n,
  Exists (fun R => (bv_unsigned (fst R) <= bv_unsigned b)%Z /\
                   (bv_unsigned b + m <= bv_unsigned (fst R) + snd R)%Z) RS ->
  (0 <= m)%Z -> apart lo n RS -> (bv_unsigned b + m <= lo \/ lo + n <= bv_unsigned b)%Z.
Proof.
  intros b m RS lo n H Hm. unfold apart. induction H as [[B N] RS' [HB1 HB2] | [B N] RS' HB IH].
  - intros Hap. apply Forall_inv in Hap. cbn [fst snd] in *. lia.
  - intros Hap. apply IH. eapply Forall_inv_tail. exact Hap.
Qed.

Lemma apart_within : forall rs RS lo n, rs_within rs RS -> apart lo n RS -> apart lo n rs.
Proof.
  intros rs RS lo n Hw Hap. induction Hw as [|[b m] rs [Hm Hb] Hrs IH]; [constructor|].
  apply apart_cons; [|exact IH]. cbn [fst snd] in *. eapply apart_within1; eauto.
Qed.

Lemma env_safe_within1 : forall ceil fs (b : word) (m : Z) RS,
  Exists (fun R => (bv_unsigned (fst R) <= bv_unsigned b)%Z /\
                   (bv_unsigned b + m <= bv_unsigned (fst R) + snd R)%Z) RS ->
  (0 <= m)%Z -> Forall (env_safe ceil fs) RS -> env_safe ceil fs (b, m).
Proof.
  intros ceil fs b m RS H Hm. unfold env_safe. cbn [fst snd]. induction H as [[B N] RS' [HB1 HB2] | [B N] RS' HB IH].
  - intros Hs. apply Forall_inv in Hs. cbn [fst snd] in *. lia.
  - intros Hs. apply IH. eapply Forall_inv_tail. exact Hs.
Qed.

Lemma within_env_safe : forall ceil fs rs RS, rs_within rs RS -> Forall (env_safe ceil fs) RS -> Forall (env_safe ceil fs) rs.
Proof.
  intros ceil fs rs RS Hw Hs. induction Hw as [|[b m] rs [Hm Hb] Hrs IH]; [constructor|].
  constructor; [|exact IH]. eapply env_safe_within1; eauto.
Qed.

Ltac solve_within :=
  unfold rs_within; repeat (apply Forall_cons; [cbn [fst snd]; split; [lia|];
    first [ apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | apply Exists_cons_tl; apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | do 3 apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | do 4 apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia
          | do 5 apply Exists_cons_tl; apply Exists_cons_hd; cbn [fst snd]; rewrite ?u_small_frame by lia; lia ] |]);
  try apply Forall_nil.

(* [comment removed for export] *)
Lemma writable_sub : forall segs mem lo n lo' n',
  writable segs mem lo n -> (lo <= lo')%Z -> (0 < n')%Z -> (lo' + n' <= lo + n)%Z -> writable segs mem lo' n'.
Proof.
  intros segs mem lo n lo' n' (W1 & W2 & W3 & W4) H1 H2 H3.
  split; [lia|]. split; [lia|]. split; [lia|].
  apply store_ok_of_all; [rewrite u_small_frame by lia; lia|].
  intros a Ha. rewrite u_small_frame in Ha by lia.
  pose proof (store_ok_all segs mem (Z.to_nat n) (Z_to_bv 64 lo)) as X.
  rewrite u_small_frame in X by lia. rewrite Z2Nat.id in X by lia.
  apply (X W3 W4 a). rewrite Z2Nat.id in Ha by lia. lia.
Qed.

Lemma mod8_add : forall a k, (a mod 8 = 0)%Z -> (k mod 8 = 0)%Z -> ((a + k) mod 8 = 0)%Z.
Proof. intros a k Ha Hk. rewrite Z.add_mod, Ha, Hk by lia. reflexivity. Qed.

Lemma mod16_sub : forall s k, (s mod 16 = 0)%Z -> (k mod 16 = 0)%Z -> ((s - k) mod 16 = 0)%Z.
Proof. intros s k Hs Hk. rewrite Zminus_mod, Hs, Hk. reflexivity. Qed.

Lemma add_lit_word : forall (A : word) (k : Z), (0 <= k)%Z -> (bv_unsigned A + k < 2 ^ 64)%Z ->
  Z_to_bv 64 (bv_unsigned A + k) = alu64 ALU_ADD A (Z_to_bv 64 k).
Proof.
  intros A k Hk H. pose proof (u64_range A). apply bv_eq. rewrite u_add64, !u_lit64a.
  rewrite (Z.mod_small k) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma shz_sub : forall M a m a' m', shz M a m -> (a' mod 8 = 0)%Z -> (a <= a')%Z -> (0 <= m')%Z -> (a' + 8 * m' <= a + 8 * m)%Z -> shz M a' m'.
Proof.
  intros M a m a' m' [Hal Hz] Hal' H1 H2 H3. split; [exact Hal'|]. intros j Hj.
  replace (SB + a' / 8 + j)%Z with (SB + a / 8 + (a' / 8 - a / 8 + j))%Z by lia. apply Hz. lia.
Qed.

(* [comment removed for export] *)
Lemma sh_addr_word : forall (P : word) (k c : Z), (bv_unsigned P mod 8 = 0)%Z -> (0 <= k)%Z ->
  (bv_unsigned P + k < 2 ^ 47)%Z -> c = (SB + k / 8)%Z ->
  alu64 ALU_ADD (alu64 ALU_SRL P (Z_to_bv 64 3)) (Z_to_bv 64 c) = Z_to_bv 64 (SB + (bv_unsigned P + k) / 8).
Proof.
  intros P k c HP Hk Hhi ->. pose proof (u64_range P). unfold SB. apply bv_eq.
  rewrite u_add64, u_srl3, !u_small by lia. rewrite Z.mod_small by lia. lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section RA.
  Variable ceil : Z.
  Variables (FPI0 : FPState) (regs0 : bvmap 5 word) (mem0 rom : word -> option byte) (ret : word).
  Variables (data : word) (len : Z) (bs : list byte) (sp T A : word) (pcs : Z) (fs : Z) (ch : chain).
  Hypothesis Hra : getr regs0 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis HPRE : a2b_pre_bo SEGS as_both ceil data len bs sp T A pcs fs ch FPI0 regs0 mem0.
  Hypothesis Hcanon : canonicalize_contract_as SEGS as_both ceil.

  #[local] Abbreviation a := (bv_unsigned A).
  #[local] Abbreviation spv := (bv_unsigned sp).
  #[local] Abbreviation t := (bv_unsigned T).

  (* [comment removed for export] *)
  Definition saved (M : word -> option byte) : Prop :=
    cell64 SEGS M (spv - 240 + 232) ret /\
    cell64 SEGS M (spv - 240 + 224) (getr regs0 8) /\ cell64 SEGS M (spv - 240 + 216) (getr regs0 9) /\
    cell64 SEGS M (spv - 240 + 208) (getr regs0 18) /\ cell64 SEGS M (spv - 240 + 200) (getr regs0 19) /\
    cell64 SEGS M (spv - 240 + 192) (getr regs0 20) /\ cell64 SEGS M (spv - 240 + 184) (getr regs0 21) /\
    cell64 SEGS M (spv - 240 + 176) (getr regs0 22) /\ cell64 SEGS M (spv - 240 + 168) (getr regs0 23) /\
    cell64 SEGS M (spv - 240 + 160) (getr regs0 24) /\ cell64 SEGS M (spv - 240 + 152) (getr regs0 25) /\
    cell64 SEGS M (spv - 240 + 144) (getr regs0 26) /\ cell64 SEGS M (spv - 240 + 136) (getr regs0 27).

  Definition fkept (FPI : FPState) : Prop :=
    forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI)) r = reg_get (fp_regs (FPState:=FPI0)) r.

  (* [comment removed for export] *)
  Definition BIG0 : list (word * Z) := [(Z_to_bv 64 (spv - 2544), 2544%Z); (Z_to_bv 64 a, 400%Z)].
  Definition BIG : list (word * Z) := BIG0 ++ fs_mod0 fs.

  (* [comment removed for export] *)
  Definition ASF (M : word -> option byte) : Prop :=
    shz M t 3 /\ shz M a 50 /\ Forall (fun off => shwz M (a + off + 12) 20) a2b_curve_offsets /\
    shz M (spv - 2544) 318 /\
    as_env SEGS ceil both_abi fs ch M /\ fs_hdr SEGS ceil both_abi fs M /\ fs_writable SEGS fs M.

  (* [comment removed for export] *)
  Definition adm (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    getr R 2 = Z_to_bv 64 (spv - 240) /\ getr R 3 = getr regs0 3 /\ getr R 4 = getr regs0 4 /\
    getr R 8 = A /\ fkept FPI /\ saved M /\ frame_mod mem0 M BIG /\
    as_data_ok ceil M data len bs /\ writable SEGS M a 400 /\ writable SEGS M (spv - 2544) 2544 /\
    ASF M /\ (exists h, acellw SEGS M (fs + FS_HINT0) h) /\ fs_flags0_but fs [] M.

  Definition Qpost : machine_state -> Prop := fun st' : machine_state =>
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      (regs_kept abi_kept regs0 regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI0)) (fp_regs (FPState:=FPI')) /\
       a2b_post_bo SEGS data len bs sp T A pcs fs ch regs0 mem0 FPI' regs' mem').

  (* [comment removed for export] *)
  Lemma pre_facts :
    (spv mod 16 = 0)%Z /\ (a mod 8 = 0)%Z /\ (appm (a) 400 /\ (0 < a)%Z) /\ (a + 400 <= ceil)%Z /\
    ((AS_STKLO <= ceil)%Z /\ (ceil + 2544 <= spv)%Z) /\ (spv <= 2 ^ 47)%Z /\
    (0 <= len < 2 ^ 26)%Z /\ (appm (bv_unsigned data) len /\ (0 < bv_unsigned data)%Z) /\ (bv_unsigned data + len <= ceil)%Z /\
    (bv_unsigned data + len <= a \/ a + 400 <= bv_unsigned data)%Z /\
    (t mod 8 = 0)%Z /\ (ceil <= t)%Z /\ (t + 24 <= 2 ^ 47)%Z /\ (spv <= t)%Z /\
    (appm (fs) FS_SIZE /\ (0 < fs)%Z) /\ (fs + FS_SIZE <= ceil)%Z /\ (fs mod 4096 = 0)%Z /\
    (fs + FS_FRAMES5 <= a)%Z /\ (a + 400 <= fs + FS_SIZE)%Z /\
    (bv_unsigned data + len <= fs \/ fs + FS_SIZE <= bv_unsigned data)%Z /\
    (bv_unsigned data mod 16 = 0)%Z /\ (pcs = 0 \/ pcs = 1)%Z.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE.
    destruct HPRE as (Hsp & HT & HA & Hpcs & Heob & Htp & Hpcs01 & Hdok & Hty & Htag & HTal & HTst & HshT & HsT &
                      WA & HAal & HAhp & HshA & Hshw & Hfs5 & HfsA & Hcurves & Hg & Hfr & Hshs &
                      Henv & Hhdr & Hfsw & Hhint & Hfl & Dfs & DA).
    pose proof Hdok as ((Hlen & Hbs & Hdnz & Hdhi & Hblob) & Hdh & Hd16 & Hshd).
    destruct Hfr as (Hst & Hal16 & WS). destruct Hhdr as (_ & _ & _ & F1 & F2 & F3). app_facts.
    unfold heapish, stackish, A2B_DB in *. app_facts.
    repeat match goal with |- appm _ _ => place_app | |- _ /\ _ => split end; try lia.
  Qed.

  Lemma pre_sp : getr regs0 2 = sp.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE. exact (proj1 HPRE). Qed.
  Lemma pre_tp : getr regs0 4 = Z_to_bv 64 0x5da970.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE. destruct HPRE as (_ & _ & _ & _ & _ & Htp & _). exact Htp. Qed.

  Ltac unfold_fs := unfold BIG, BIG0, fs_mod0, env_safe, SB, AS_SB, FS_HINT0, FS_SSL, FS_NEEDSGC,
    FS_FLAGS0, FS_FLAGS0_LEN, FS_FRAMES0, FS_FRAMES_LEN, FS_SHFRAMES_LEN, FS_SIZE, FS_FRAMES5 in *.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma BIG_env_safe : Forall (env_safe ceil fs) BIG.
  Proof using ceil FPI0 regs0 mem0 rom data len bs sp T A pcs fs ch HPRE.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & _). app_facts.
    unfold_fs.
    repeat (apply Forall_cons; [cbn [fst snd]; rewrite u_small_frame by clia; first [clia | dlia]|]). apply Forall_nil.
  Qed.

  (* [comment removed for export] *)
  Lemma apart_BIG_shadow : forall x n, (0 <= n)%Z -> (0 <= x)%Z -> (x + 8 * n <= 2 ^ 47)%Z ->
    (x + 8 * n <= fs + FS_FRAMES0 \/ fs + FS_FRAMES0 + FS_FRAMES_LEN + 8 <= x)%Z ->
    apart (SB + x / 8) n BIG.
  Proof using ceil FPI0 regs0 mem0 rom data len bs sp T A pcs fs ch HPRE.
    intros x n Hn Hx Hhi Hc.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & _). app_facts.
    pose proof (app_sh_lit _ _ (proj1 P15)) as Fsh.
    unfold_fs.
    unfold apart. repeat (apply Forall_cons; [cbn [fst snd]; rewrite u_small_frame by clia; first [clia | dlia]|]). apply Forall_nil.
  Qed.

  Lemma shwz_frame_BIG : forall M M' rs x n, frame_mod M M' rs -> rs_within rs BIG -> shwz M x n ->
    (0 <= x)%Z -> (0 < n)%Z -> (x + n + 8 <= 2 ^ 47)%Z -> (fs + FS_FRAMES0 + FS_FRAMES_LEN + 72 <= x)%Z -> shwz M' x n.
  Proof using ceil FPI0 regs0 mem0 rom data len bs sp T A pcs fs ch HPRE.
    intros M M' rs x n Hf Hw Hs Hx Hn Hhi Hlo.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & _). app_facts.
    pose proof (app_sh_lit _ _ (proj1 P15)) as Fsh.
    eapply shwz_frame; [exact Hf | exact Hs | lia | lia |].
    eapply apart_within; [exact Hw|].
    unfold_fs.
    unfold apart. repeat (apply Forall_cons; [cbn [fst snd]; rewrite u_small_frame by clia; first [clia | dlia]|]). apply Forall_nil.
  Qed.

  Lemma offsets_bound : forall o, In o a2b_curve_offsets ->
    (0 <= o)%Z /\ (o + 32 <= 400)%Z /\ (o mod 8 = 0)%Z /\
    ((o + 32 <= 128)%Z \/ (152 <= o /\ o + 32 <= 248)%Z \/ (304 <= o)%Z).
  Proof using .
    intros o Ho. cbn in Ho. repeat (destruct Ho as [<-|Ho]); try (destruct Ho as []);
      (split; [lia|]; split; [lia|]; split; [reflexivity|]; lia).
  Qed.

  (* [comment removed for export] *)
  Lemma ASF_frame : forall M M' rs, ASF M -> frame_mod M M' rs -> rs_within rs BIG -> ASF M'.
  Proof using ceil FPI0 regs0 mem0 rom data len bs sp T A pcs fs ch HPRE.
    intros M M' rs (S1 & S2 & S3 & S4 & S5 & S6 & S7) Hf Hw.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & _). app_facts.
    pose proof (app_sh_lit _ _ (proj1 P15)) as Fsh.
    pose proof (within_env_safe ceil fs rs BIG Hw BIG_env_safe) as Hs.
    unfold FS_SIZE, FS_FRAMES5, FS_FRAMES0, FS_FRAMES_LEN in *.
    split; [eapply shz_frame; [exact Hf | exact S1 | lia | lia | eapply apart_within; [exact Hw | apply apart_BIG_shadow; unfold FS_FRAMES0, FS_FRAMES_LEN; lia]]|].
    split; [eapply shz_frame; [exact Hf | exact S2 | lia | lia | eapply apart_within; [exact Hw | apply apart_BIG_shadow; unfold FS_FRAMES0, FS_FRAMES_LEN; lia]]|].
    split.
    { apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) S3 o Ho) as Hz. cbv beta in Hz.
      pose proof (offsets_bound o Ho) as (B1 & B2 & B3 & _).
      eapply shwz_frame_BIG; [exact Hf | exact Hw | exact Hz | lia | lia | lia | unfold FS_FRAMES0, FS_FRAMES_LEN; lia]. }
    split; [eapply shz_frame; [exact Hf | exact S4 | lia | lia | eapply apart_within; [exact Hw | apply apart_BIG_shadow; unfold FS_FRAMES0, FS_FRAMES_LEN; lia]]|].
    split; [eapply as_env_frame; [apply both_abi_low | ceil_lo | fs_app | exact Hf | exact Hs | exact S5]|].
    split; [eapply fs_hdr_frame; [apply both_abi_low | ceil_lo | exact Hf | exact Hs | | exact S6]|].
    { eapply apart_within; [exact Hw|]. unfold_fs.
      unfold apart. repeat (apply Forall_cons; [cbn [fst snd]; rewrite u_small_frame by clia; first [clia | dlia]|]). apply Forall_nil. }
    eapply fs_writable_frame; [exact Hf | exact S7].
  Qed.

  (* [comment removed for export] *)
  Lemma hint_flags_frame0 : forall M M' rs,
    (exists h, acellw SEGS M (fs + FS_HINT0) h) -> fs_flags0_but fs [] M ->
    frame_mod M M' rs -> rs_within rs BIG0 ->
    (exists h, acellw SEGS M' (fs + FS_HINT0) h) /\ fs_flags0_but fs [] M'.
  Proof using ceil FPI0 regs0 mem0 rom data len bs sp T A pcs fs ch HPRE.
    intros M M' rs [h Hh] Hfl Hf Hw.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & _). app_facts.
    unfold FS_SIZE, FS_FRAMES5 in *.
    split.
    - exists h. eapply acellw_frame; [exact Hf | exact Hh | unfold FS_HINT0; lia | unfold FS_HINT0; lia |].
      eapply apart_within; [exact Hw|]. unfold BIG0, FS_HINT0. solve_apart.
    - eapply fs_flags0_but_frame; [exact Hf | exact Hfl | lia | unfold FS_SIZE; lia |].
      intros i Hi _. split; [intros []|]. eapply apart_within; [exact Hw|]. unfold BIG0, FS_FLAGS0, FS_FLAGS0_LEN in *. solve_apart.
  Qed.

  Lemma within_BIG0 : forall rs, rs_within rs BIG0 -> rs_within rs BIG.
  Proof using sp A fs.
    intros rs H. unfold rs_within in *. eapply Forall_impl; [|exact H]. intros [b m] [Hm Hb]. split; [exact Hm|].
    unfold BIG. apply Exists_app. left. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma adm_frame : forall (FPI FPI' : FPState) R R' M M' rs,
    adm FPI R M -> frame_mod M M' rs -> rs_within rs BIG -> apart (spv - 104) 104 rs ->
    (exists h, acellw SEGS M' (fs + FS_HINT0) h) -> fs_flags0_but fs [] M' ->
    getr R' 2 = getr R 2 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
    getr R' 8 = getr R 8 ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    adm FPI' R' M'.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE.
    intros FPI FPI' R R' M M' rs (A2 & A3 & A4 & A8 & AF & AS & AFR & AD & AWA & AWS & AASF & AH & AFL)
           Hf Hw Hap Hh Hfl E2 E3 E4 E8 EF.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & _). app_facts.
    assert (HfB : frame_mod M M' BIG) by (eapply frame_mod_within; eauto).
    split; [rewrite E2; exact A2|]. split; [rewrite E3; exact A3|]. split; [rewrite E4; exact A4|].
    split; [rewrite E8; exact A8|].
    split; [intros r Hr; rewrite (EF r Hr); apply AF; exact Hr|].
    split.
    { unfold saved in *.
      destruct AS as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
      repeat match goal with |- _ /\ _ => split end;
        (eapply cell64_frame; [exact Hf | eassumption | clia | clia | eapply apart_sub; [exact Hap|clia|clia|clia]]). }
    split; [eapply frame_mod_trans_same; [exact AFR | exact HfB]|].
    split.
    { destruct AD as (D1 & D2 & D3 & D4). split; [|split; [exact D2|split; [exact D3|]]].
      - eapply data_ok_frame; [exact HfB | exact D1 |].
        unfold_fs.
            solve_apart.
          - eapply shdata_frame; [exact HfB | exact D4 | lia | lia | lia |].
        apply apart_BIG_shadow; unfold FS_FRAMES0, FS_FRAMES_LEN, FS_SIZE in *; [lia|lia|lia|].
            lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    split; [eapply writable_frame; [exact Hf | exact AWA]|].
    split; [eapply writable_frame; [exact Hf | exact AWS]|].
    split; [eapply ASF_frame; [exact AASF | exact Hf | exact Hw]|].
    split; [exact Hh | exact Hfl].
  Qed.

  (* [comment removed for export] *)
  Lemma adm_frame0 : forall (FPI FPI' : FPState) R R' M M' rs,
    adm FPI R M -> frame_mod M M' rs -> rs_within rs BIG0 -> apart (spv - 104) 104 rs ->
    getr R' 2 = getr R 2 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
    getr R' 8 = getr R 8 ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    adm FPI' R' M'.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE.
    intros FPI FPI' R R' M M' rs HADM Hf Hw Hap E2 E3 E4 E8 EF.
    pose proof HADM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AH & AFL).
    destruct (hint_flags_frame0 M M' rs AH AFL Hf Hw) as [Hh Hfl].
    apply (adm_frame FPI FPI' R R' M M' rs HADM Hf (within_BIG0 rs Hw) Hap Hh Hfl E2 E3 E4 E8 EF).
  Qed.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition base_vals : list word :=
    [ret; getr regs0 8; getr regs0 9; getr regs0 18; getr regs0 19; getr regs0 20; getr regs0 21;
     getr regs0 22; getr regs0 23; getr regs0 24; getr regs0 25; getr regs0 26; getr regs0 27;
     data; Z_to_bv 64 len].

  (* [comment removed for export] *)
  Definition kn_adm : list kentry :=
    [KWord (SA (EVar 2) 232) 8 (EVar 64); KWord (SA (EVar 2) 224) 8 (EVar 65); KWord (SA (EVar 2) 216) 8 (EVar 66);
     KWord (SA (EVar 2) 208) 8 (EVar 67); KWord (SA (EVar 2) 200) 8 (EVar 68); KWord (SA (EVar 2) 192) 8 (EVar 69);
     KWord (SA (EVar 2) 184) 8 (EVar 70); KWord (SA (EVar 2) 176) 8 (EVar 71); KWord (SA (EVar 2) 168) 8 (EVar 72);
     KWord (SA (EVar 2) 160) 8 (EVar 73); KWord (SA (EVar 2) 152) 8 (EVar 74); KWord (SA (EVar 2) 144) 8 (EVar 75);
     KWord (SA (EVar 2) 136) 8 (EVar 76);
     KImg 0x20cf8 0x20f00;
     KRange (EVar 2) (AS_STKLO + 2304) (2 ^ 47 - 240); KAlign (EVar 2) 16; KWr (SA (EVar 2) (-2304)) 2544;
     KRange (EVar 8) 1 (2 ^ 47 - 400); KAlign (EVar 8) 8; KWr (SA (EVar 8) 0) 400;
     KZero (SA (EAlu ALU_SRL (EVar 8) (ELit 3)) SB) (ELit 50);
     KRange (EVar 77) 1 (2 ^ 47 - 2048); KAlign (EVar 77) 16; KRange (EVar 78) 0 67108864;
     KDisj (SA (EVar 8) 0) 400 ZSH ZSHL; KDisj (SA (EVar 8) 0) 400 ZIMG ZIMGL; KDisj (SA (EVar 8) 0) 400 (SA (EVar 2) (-2288)) 2528].

  (* [comment removed for export] *)
  Definition kn_end : list kentry := [KShad (EVar 77) (EVar 78) SB; KBlobD (SA (EVar 77) 0) (EVar 78) 0;
                                       KRange (EAlu ALU_ADD (EVar 77) (EVar 78)) 0 (2 ^ 47 - 2048)].

  Lemma kn_adm_ok : forall (FPI : FPState) R M extra,
    adm FPI R M ->
    know_ok SEGS (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_vals ++ extra)) (blobs_ev [bs])) M kn_adm.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M extra (A2 & A3 & A4 & A8 & AF & AS & AFR & AD & AWA & AWS & AASF & AH & AFL).
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & _). app_facts.
    set (E := Env _ _). unfold base_vals in E.
    assert (U2 : bv_unsigned (getr R 2) = (spv - 240)%Z) by (rewrite A2, u_small by lia; lia).
    destruct AS as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13).
    destruct AASF as (S1 & S2 & S3 & S4 & (S5a & S5b & S5c & S5d) & S6 & S7). destruct AD as (D1 & D2 & D3 & D4).
    unfold kn_adm.
    repeat apply Forall_cons; try apply Forall_nil.
    all: try (eapply (kword_intro SEGS E M (EVar 2) (getr R 2) _ 8 _ _);
           [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia |
            rewrite U2; unfold cell64, cell in *;
            match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ =>
              first [ replace x with (spv - 240 + 232)%Z by ring; eassumption
                    | replace x with (spv - 240 + 224)%Z by ring; eassumption
                    | replace x with (spv - 240 + 216)%Z by ring; eassumption
                    | replace x with (spv - 240 + 208)%Z by ring; eassumption
                    | replace x with (spv - 240 + 200)%Z by ring; eassumption
                    | replace x with (spv - 240 + 192)%Z by ring; eassumption
                    | replace x with (spv - 240 + 184)%Z by ring; eassumption
                    | replace x with (spv - 240 + 176)%Z by ring; eassumption
                    | replace x with (spv - 240 + 168)%Z by ring; eassumption
                    | replace x with (spv - 240 + 160)%Z by ring; eassumption
                    | replace x with (spv - 240 + 152)%Z by ring; eassumption
                    | replace x with (spv - 240 + 144)%Z by ring; eassumption
                    | replace x with (spv - 240 + 136)%Z by ring; eassumption ] end]).
    - apply kimg_intro; [lia|lia|]. intros i Hi. apply (S5c 0x20cf8%Z 0x20f00%Z i); [first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)] | exact Hi].
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite U2; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite U2. apply mod16_sub; [exact P1|reflexivity].
    - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-2304) 2544); [cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia |].
      rewrite U2. replace (spv - 240 + -2304)%Z with (spv - 2544)%Z by lia. exact (proj2 (proj2 (proj2 AWS))).
    - apply krange_intro; cbn [edenot]; ev_simpl E; rewrite A8; lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. rewrite A8. exact P2.
    - apply (kwr_intro SEGS E M (EVar 8) A 0 400); [cbn [edenot]; ev_simpl E; exact A8 | lia | lia | lia |].
      rewrite Z.add_0_r. exact (proj2 (proj2 (proj2 AWA))).
    - apply (kzero_shz_intro SEGS E M (EVar 8) A 50); [cbn [edenot]; ev_simpl E; exact A8 | exact S2 | lia | lia].
    - apply krange_intro; cbn [edenot]; ev_simpl E. lia.
    - apply kalign_intro; [lia|]. cbn [edenot]; ev_simpl E. exact P21.
    - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia.
    - kdisj_place.
    - kdisj_place.
    - kdisj_place.
  Qed.

  Lemma kn_end_ok : forall (FPI : FPState) R M extra,
    adm FPI R M ->
    know_ok SEGS (Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_vals ++ extra)) (blobs_ev [bs])) M kn_end.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M extra (A2 & A3 & A4 & A8 & AF & AS & AFR & AD & AWA & AWS & AASF & AH & AFL).
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _). app_facts.
    set (E := Env _ _). unfold base_vals in E. destruct AD as (D1 & D2 & D3 & D4).
    pose proof D1 as (Hlen & Hbs & Hdnz & Hdhi & Hblob).
    constructor; [|constructor; [|constructor; [|constructor]]].
    - apply (kshad_intro SEGS E M (EVar 77) (EVar 78) data len); [cbn [edenot]; ev_simpl E; reflexivity | cbn [edenot]; ev_simpl E; rewrite u_small by lia; reflexivity | lia | lia | exact D4].
    - cbn [kentry_ok]; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; ev_simpl E.
      rewrite u_small by lia. split; [lia|]. split; [exact Hbs|]. intros i Hi. rewrite Z.add_0_r. apply Hblob. exact Hi.
    - destruct D2 as [D2a D2b]. eapply krange_add_intro; [place_den | place_den | rewrite ?u_small by lia; lia | lia].
  Qed.

  (* [comment removed for export] *)
  Ltac adm_facts HADM :=
    pose proof HADM as (A2 & A3 & A4 & A8 & AF & AS & AFR & AD & AWA & AWS & AASF & AH & AFL);
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & _);
    assert (U2 : bv_unsigned (getr _ 2) = (spv - 240)%Z) by (rewrite A2, u_small by lia; lia).

  (* [comment removed for export] *)
  Ltac pkg HADM extra kx ktac :=
    lazymatch goal with
    | |- runs_to _ (@mkst ?FPI ?R _ ?M _) _ =>
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ base_vals ++ extra)) (blobs_ev [bs]));
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs]));
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs]));
      pose proof (HR : id _) as HR0; pose proof (HF : id _) as HF0;
      let HK1 := fresh "HK1" in let HK2 := fresh "HK2" in let HK3 := fresh "HK3" in
      pose proof (kn_adm_ok FPI R M extra HADM) as HK1; change (know_ok SEGS E M kn_adm) in HK1;
      assert (HK2 : know_ok SEGS E M kx); [ktac|];
      pose proof (kn_end_ok FPI R M extra HADM) as HK3; change (know_ok SEGS E M kn_end) in HK3;
      pose proof (know_ok_app SEGS E M kn_adm (kx ++ kn_end) HK1 (know_ok_app SEGS E M kx kn_end HK2 HK3)) as HK;
      clear HK1 HK2 HK3;
      cbv beta delta [kn_adm kn_end] in HK; cbn [app] in HK
    end.

  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kept_int :=
    lazymatch goal with HR : regs_ok ?E _ ?R' |- regs_kept abi_kept regs0 ?R' =>
      intros r Hr; cbn [abi_kept In] in Hr;
      repeat (destruct Hr as [<-|Hr]);
      [ regv_lin HR (2%bv:reg);
        match goal with U2 : bv_unsigned (getr _ 2) = _ |- _ => rewrite U2 end;
        rewrite pre_sp; apply bv_eq; rewrite u_small by lia; lia
      | regv HR (3%bv:reg); assumption
      | regv HR (4%bv:reg); assumption
      | .. ];
      try (destruct Hr as []);
      lazymatch goal with |- getr _ ?r = _ => regv HR r; try reflexivity; try assumption end
    end.

  Ltac kept_fp :=
    lazymatch goal with
    | HF : fregs_ok ?E ?sfr' (@fp_regs ?I'), HF0 : id (fregs_ok _ ?sfr0 ?fr), AF : fkept _ |- _ =>
      intros r Hr;
      rewrite (fregs_same_on E sfr0 sfr' fr _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity) r Hr);
      apply AF; exact Hr
    end.

  (* [comment removed for export] *)
  Lemma exitk : forall (FPI : FPState) R M (rv : Z),
    adm FPI R M -> getr R 23 = Z_to_bv 64 rv ->
    (rv = 0%Z \/ (rv = 1%Z /\ Forall (fun off => curve_ok SEGS M data len (a + off)) a2b_curve_offsets /\ a2b_grid_ok SEGS M data len a)) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x8459c) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE.
    intros FPI R M rv HADM H23 Hrv. adm_facts HADM.
    pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
    run_fp 40%nat (@nil Z) noscr true.
    fin_ret.
    unfold Qpost.
    lazymatch goal with |- context [@mkst ?I ?R' ?pc ?M' _] => exists I, R', M' end.
    split; [regv HR (1%bv:reg); reflexivity|].
    split; [kept_int|].
    split; [kept_fp|].
    unfold a2b_post_bo. cbv zeta. change A2B_DB with 2544%Z.
    split; [subst; exact AFR|].
    split; [subst; exact AFL|]. split; [subst; exact AH|].
    exists rv. split; [regv HR (10%bv:reg); rewrite H23; reflexivity|].
    destruct Hrv as [-> | (-> & Hall & Hgrid)].
    - split; [left; reflexivity|]. intros H01; exfalso; lia.
    - split; [right; reflexivity|]. intros _. subst. split; [exact Hall | exact Hgrid].
  Qed.

  (* [comment removed for export] *)
  Lemma failk : forall (FPI : FPState) R M,
    adm FPI R M -> runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84598) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE.
    intros FPI R M HADM. adm_facts HADM.
    pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
    run_fp 6%nat [0x8459c%Z] noscr true.
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
      apply (exitk I1 R1 M1 0%Z); [| regv HR (23%bv:reg); reflexivity | left; reflexivity] end.
    subst. apply (adm_frame0 FPI _ R _ M M []); try assumption; try (apply frame_mod_refl); try (apply Forall_nil).
    - regv HR (2%bv:reg); reflexivity.
    - regv HR (3%bv:reg); reflexivity.
    - regv HR (4%bv:reg); reflexivity.
    - regv HR (8%bv:reg); reflexivity.
    - exact (fregs_same_on E _ _ _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)).
  Qed.

  (* [comment removed for export] *)
  Lemma failk' : forall (FPI : FPState) R M,
    adm FPI R M -> getr R 23 = Z_to_bv 64 0 ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x8459c) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE. intros FPI R M HADM H23. apply (exitk FPI R M 0%Z HADM H23). left; reflexivity. Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Definition chain_inv (ic mc : Z) (M : word -> option byte) : Prop :=
    cell32 SEGS M (a + 144) ic /\ cell32 SEGS M (a + 296) mc /\ cell32 SEGS M (a + 300) 3 /\
    (0 <= ic <= 4)%Z /\ (mc = 0 \/ mc = 3)%Z /\
    Forall (fun off => curve_ok SEGS M data len (a + off)) a2b_curve_offsets /\
    a2b_grid_ok SEGS M data len a.

  Lemma a2b_grid_ok_frame : forall M M' rs,
    a2b_grid_ok SEGS M data len a -> frame_mod M M' rs ->
    apart (a + 128) 24 rs -> apart (a + 296) 8 rs -> a2b_grid_ok SEGS M' data len a.
  Proof using ceil FPI0 regs0 mem0 data len bs sp T A pcs fs ch HPRE.
    intros M M' rs (ic & oc & gps & g8 & g16 & Hic & Hoc & Hicr & Hlen & Hgps & Hgp & Hg8 & Hg16 & Hrest) Hf Hap1 Hap2.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & _). app_facts.
    exists ic, oc, gps, g8, g16.
    split; [eapply cell32_frame; [exact Hf|exact Hic|lia|lia|]; eapply apart_sub; [exact Hap1|lia|lia|lia]|].
    split; [eapply cell32_frame; [exact Hf|exact Hoc|lia|lia|]; eapply apart_sub; [exact Hap2|lia|lia|lia]|].
    split; [exact Hicr|]. split; [exact Hlen|]. split; [exact Hgps|].
    split.
    { intros i Hi. eapply cell8_frame; [exact Hf|exact (Hgp i Hi)|lia|lia|]. eapply apart_sub; [exact Hap1|lia|lia|lia]. }
    split; [eapply cell64_frame; [exact Hf|exact Hg8|lia|lia|]; eapply apart_sub; [exact Hap1|lia|lia|lia]|].
    split; [eapply cell64_frame; [exact Hf|exact Hg16|lia|lia|]; eapply apart_sub; [exact Hap1|lia|lia|lia]|].
    exact Hrest.
  Qed.

  (* [comment removed for export] *)
  Lemma offsets_apart : forall o o', In o a2b_curve_offsets -> In o' a2b_curve_offsets ->
    o = o' \/ (o + 32 <= o')%Z \/ (o' + 32 <= o)%Z.
  Proof using .
    intros o o' Ho Ho'. cbn in Ho, Ho'.
    repeat (destruct Ho as [<-|Ho]); try (destruct Ho as []);
    repeat (destruct Ho' as [<-|Ho']); try (destruct Ho' as []); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma chain_inv_canon : forall ic mc M M' (w : word) o,
    chain_inv ic mc M -> In o a2b_curve_offsets ->
    frame_mod M M' ([(w, 2272%Z); (Z_to_bv 64 (a + o), 32%Z)] ++ fs_mod0 fs) ->
    (bv_unsigned w + 2272 <= a \/ a + 400 <= bv_unsigned w)%Z ->
    curve_ok SEGS M' data len (a + o) ->
    chain_inv ic mc M'.
  Proof using ceil FPI0 regs0 mem0 rom data len bs sp T A pcs fs ch HPRE.
    intros ic mc M M' w o (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid) Ho Hf Hw Hc.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & _). app_facts.
    pose proof (offsets_bound o Ho) as (B1 & B2 & B3 & B4).
    assert (AP : forall lo n, (0 <= lo)%Z -> (a + o + 32 <= lo \/ lo + n <= a + o)%Z -> (a <= lo)%Z -> (lo + n <= a + 400)%Z ->
                 apart lo n ([(w, 2272%Z); (Z_to_bv 64 (a + o), 32%Z)] ++ fs_mod0 fs)).
    { intros lo n H1 H2 H3 H4. unfold_fs. cbn [app]. unfold apart. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
      - lia.
      - rewrite u_small_frame by lia. lia.
      - rewrite u_small_frame by lia. lia.
      - rewrite u_small_frame by lia. lia.
      - rewrite u_small_frame by lia. lia.
      - Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
        rewrite u_small_frame by lia. pose proof (app_sh_lit _ _ (proj1 P15)) as Fsh. destruct Fsh as [Fsh|Fsh]; clia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    split; [eapply cell32_frame; [exact Hf|exact C1|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C2|lia|lia|apply AP; lia]|].
    split; [eapply cell32_frame; [exact Hf|exact C3|lia|lia|apply AP; lia]|].
    split; [exact Hic|]. split; [exact Hmc|].
    split.
    - apply Forall_forall. intros o' Ho'.
      pose proof (proj1 (Forall_forall _ _) Hall o' Ho') as Hc'. cbv beta in Hc'.
      destruct (Z.eq_dec o' o) as [->|Hne]; [exact Hc|].
      pose proof (offsets_apart o o' Ho Ho') as HA. pose proof (offsets_bound o' Ho') as (B1' & B2' & _).
      eapply curve_ok_frame; [exact Hf|exact Hc'|lia|lia|]. apply AP; lia.
    - eapply a2b_grid_ok_frame; [exact Hgrid|exact Hf|apply AP; lia|apply AP; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma canon_pre_at : forall (FPI : FPState) R M ic mc o h,
    adm FPI R M -> chain_inv ic mc M -> In o a2b_curve_offsets ->
    getr R 10 = Z_to_bv 64 (a + o) -> acellw SEGS M (fs + FS_HINT0) h ->
    canon_pre_as SEGS as_both ceil data len bs (Z_to_bv 64 (spv - 240)) (Z_to_bv 64 (a + o)) fs h ch FPI R M.
  Proof using ceil FPI0 regs0 mem0 ret data len bs sp T A pcs fs ch HPRE.
    intros FPI R M ic mc o h HADM (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid) Ho H10 Hh. adm_facts HADM.
    pose proof pre_facts as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & _). app_facts.
    pose proof (offsets_bound o Ho) as (B1 & B2 & B3 & B4).
    destruct AASF as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
    unfold canon_pre_as, as_frame, stackish, heapish. cbv zeta. change (CANON_D / 8)%Z with 284%Z. change CANON_D with 2272%Z. cbn [al_abi as_both].
    rewrite !u_small by lia.
    split; [exact A2|]. split; [exact H10|]. split; [rewrite A4; exact pre_tp|].
    split.
    { split; [lia|]. split; [apply mod16_sub; [exact P1|reflexivity]|].
      eapply writable_sub; [exact AWS|lia|lia|lia]. }
    split; [eapply shz_sub; [exact S4 | | lia | lia | lia]; replace (spv - 240 - 2272)%Z with (spv - 2544 + 4 * 8)%Z by lia; rewrite Z_mod_plus_full; exact (proj1 S4)|].
    split; [apply mod8_add; [exact P2|exact B3]|].
    split; [plc|].
    split; [eapply writable_sub; [exact AWA|lia|lia|lia]|].
    split; [eapply shz_sub; [exact S2 | apply mod8_add; [exact P2|exact B3] | lia | lia | lia]|].
    split; [exact (proj1 (Forall_forall _ _) S3 o Ho)|].
    split; [lia|]. split; [lia|].
    split; [exact (proj1 (Forall_forall _ _) Hall o Ho)|].
    split; [exact AD|]. split; [exact P20|]. split; [lia|].
    split; [exact S5|]. split; [exact S6|]. split; [exact S7|]. split; [exact Hh|]. exact AFL.
  Qed.

  (* [comment removed for export] *)
  Lemma adm_canon : forall (FPI FPI' : FPState) R R' M M' o,
    adm FPI R M -> In o a2b_curve_offsets ->
    frame_mod M M' ([(Z_to_bv 64 (spv - 240 - 2272), 2272%Z); (Z_to_bv 64 (a + o), 32%Z)] ++ fs_mod0 fs) ->
    fs_flags0_but fs [] M' -> (exists h', acellw SEGS M' (fs + FS_HINT0) h') ->
    regs_kept abi_kept R R' ->
    (forall r, In r abi_fkept -> reg_get (fp_regs (FPState:=FPI')) r = reg_get (fp_regs (FPState:=FPI)) r) ->
    adm FPI' R' M'.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch HPRE.
    intros FPI FPI' R R' M M' o HADM Ho Hf Hfl Hh Hk Hfk.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & _). app_facts.
    pose proof (offsets_bound o Ho) as (B1 & B2 & _).
    apply (adm_frame FPI FPI' R R' M M' _ HADM Hf).
    - unfold_fs. cbn [app]. solve_within.
    - unfold_fs. cbn [app].
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      solve_apart.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
    - exact Hh.
    - exact Hfl.
    - apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)].
    - apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)].
    - apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)].
    - apply Hk; first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)].
    - exact Hfk.
  Qed.

  Lemma chain_inv_canon' : forall ic mc M M' o,
    chain_inv ic mc M -> In o a2b_curve_offsets ->
    frame_mod M M' ([(Z_to_bv 64 (spv - 240 - 2272), 2272%Z); (Z_to_bv 64 (a + o), 32%Z)] ++ fs_mod0 fs) ->
    curve_ok SEGS M' data len (a + o) ->
    chain_inv ic mc M'.
  Proof using ceil FPI0 regs0 mem0 rom data len bs sp T A pcs fs ch HPRE.
    intros ic mc M M' o HCI Ho Hf Hc.
    pose proof pre_facts as (P1 & P2 & P3 & P4 & P5 & P6 & _). app_facts.
    eapply (chain_inv_canon ic mc M M' _ o HCI Ho Hf); [|exact Hc].
    rewrite u_small by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac subst_mems :=
    repeat match goal with H : @eq (word -> option byte) ?x _ |- _ => is_var x; subst x end.

  Ltac adm_now HADM HADM1 :=
    subst_mems;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1, HF : fregs_ok _ ?sfr (@fp_regs ?I1), HF0 : id (fregs_ok _ ?sfr0 (@fp_regs ?I0))
      |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      lazymatch type of HADM with adm _ ?R ?M0 =>
        assert (HADM1 : adm I1 R1 M1);
        [ apply (adm_frame0 I0 I1 R R1 M0 M1 [] HADM);
          [ apply frame_mod_refl
          | apply Forall_nil
          | apply Forall_nil
          | regv HR (2%bv:reg); reflexivity
          | regv HR (3%bv:reg); reflexivity
          | regv HR (4%bv:reg); reflexivity
          | regv HR (8%bv:reg); reflexivity
          | exact (fregs_same_on E sfr0 sfr _ _ abi_fkept HF0 HF ltac:(vm_compute; reflexivity)) ]
        | ]
      end
    end.

  (* [comment removed for export] *)
  Ltac call_canon o HADM HCI retpc k :=
    let HADM1 := fresh "HADMc" in
    adm_now HADM HADM1;
    lazymatch goal with
    | HR : regs_ok ?E ?sr ?R1 |- runs_to _ (@mkst ?I1 _ _ ?M1 _) _ =>
      let Ho := fresh "Ho" in let h := fresh "h" in let Hh := fresh "Hh" in
      assert (Ho : In o a2b_curve_offsets) by (first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)]);
      destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HADM1)))))))))))) as [h Hh];
      eapply rt_call;
      [ eapply (Hcanon data len bs (Z_to_bv 64 (spv - 240)) (Z_to_bv 64 (a + o)) fs h ch I1 R1 M1 rom (Z_to_bv 64 retpc));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | eapply (canon_pre_at I1 R1 M1 _ _ o h HADM1); [exact HCI | exact Ho | regv_lin HR (10%bv:reg);
            match goal with A8 : getr _ 8 = A |- _ => rewrite A8 end; f_equal; lia | exact Hh] ]
      | cbv beta; let I' := fresh "FPI" in let R' := fresh "R" in let M' := fresh "M" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hfr := fresh "Hfr" in let Hc := fresh "Hcv" in
        let Hfl := fresh "Hfl" in let Hh' := fresh "Hh'" in
        intros I' R' M' (Hkeep & Hfkeep & Hfr & Hc & Hfl & Hh');
        change CANON_D with 2272%Z in Hfr;
        rewrite (u_small (spv - 240)) in Hfr by lia; rewrite (u_small (a + o)) in Hc by lia;
        let HADM' := fresh "HADM" in let HCI' := fresh "HCI" in
        pose proof (adm_canon I1 I' R1 R' M1 M' o HADM1 Ho Hfr Hfl Hh' Hkeep Hfkeep) as HADM';
        lazymatch type of HCI with chain_inv ?ic ?mc _ =>
          assert (HCI' : chain_inv ic mc M');
          [ eapply (chain_inv_canon' ic mc M1 M' o); [exact HCI | exact Ho | exact Hfr | exact Hc]
          | k I' R' M' HADM' HCI' Hkeep ] end ]
    end.

  (* [comment removed for export] *)
  Ltac pkg_cell HADM off v C :=
    pkg HADM (@nil word) [KWord (SA (EVar 8) off) 4 (ELit v)]
      ltac:(constructor; [|constructor];
            lazymatch goal with |- kentry_ok _ ?E ?M _ =>
              eapply (kword_intro SEGS E M (EVar 8) A off 4 (ELit v) (Z_to_bv 64 v));
              [ cbn [edenot]; ev_simpl E; match goal with A8 : getr _ 8 = A |- _ => exact A8 end
              | reflexivity | lia | lia | lia | lia | exact (proj2 C)] end).

  (* [comment removed for export] *)
  #[local] Abbreviation SHX k c := (EAlu ALU_ADD (EAlu ALU_SRL (EVar 8) (ELit 3)) (ELit (SB + c)))  (only parsing).
  Ltac pin_sb HR H24 := pin_reg HR (24%bv:reg) (ELit SB) by (cbn [edenot]; exact H24).
  Ltac pin_s1 HR H9 k :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR (9%bv:reg) (EAlu ALU_ADD (EVar 8) (ELit k))
        by (cbn [edenot]; ev_simpl E; match goal with A8 : getr _ 8 = A |- _ => rewrite A8 end; rewrite H9; apply add_lit_word; lia)
    end.
  (* [comment removed for export] *)
  Ltac pin_ak HR r H k :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EAlu ALU_ADD (EVar 8) (ELit k))
        by (cbn [edenot]; ev_simpl E; match goal with A8 : getr _ 8 = A |- _ => rewrite A8 end; rewrite H; apply add_lit_word; lia)
    end.
  Ltac pin_sh HR r H k c :=
    lazymatch type of HR with regs_ok ?E _ _ =>
      pin_reg HR r (EAlu ALU_ADD (EAlu ALU_SRL (EVar 8) (ELit 3)) (ELit (SB + c)))
        by (cbn [edenot]; ev_simpl E; match goal with A8 : getr _ 8 = A |- _ => rewrite A8 end; rewrite H; symmetry;
            apply (sh_addr_word A k); first [assumption | reflexivity | lia])
    end.

  (* [comment removed for export] *)
  Ltac kreg Hkeep r :=
    lazymatch goal with HR : regs_ok _ _ _, A8 : getr _ 8 = A |- _ =>
      rewrite (Hkeep r ltac:(first [solve [cbn; repeat (first [left; reflexivity | right])] | (cbn; tauto)])); regv HR r; rewrite ?A8;
      first [ reflexivity | assumption
            | symmetry; apply add_lit_word; lia
            | apply (sh_addr_word A); first [assumption | reflexivity | lia] ]
    end.

  (* [comment removed for export] *)
  Lemma out4 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 23 = Z_to_bv 64 1 ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x8457c) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE.
    intros FPI R M ic mc HADM HCI H23. adm_facts HADM.
    pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
    run_fp 4%nat [0x8459c%Z] noscr true.
    adm_now HADM HADM1.
    lazymatch goal with |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
      apply (exitk I1 R1 M1 1%Z HADM1); [regv HR (23%bv:reg); exact H23|] end.
    right. split; [reflexivity|]. destruct HCI as (_ & _ & _ & _ & _ & Hall & Hgrid). split; [exact Hall | exact Hgrid].
  Qed.

  (* [comment removed for export] *)
  Lemma out3 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 23 = Z_to_bv 64 1 ->
    getr R 9 = Z_to_bv 64 (a + 300) -> getr R 24 = Z_to_bv 64 (SB + (a + 300) / 8) -> getr R 18 = Z_to_bv 64 (a + 304) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84558) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI H23 H9 H24 H18. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    pkg_cell HADM 300%Z 3%Z C3.
    pin_s1 HR H9 300%Z. pin_sh HR (24%bv:reg) H24 300%Z 37%Z. pin_ak HR (18%bv:reg) H18 304%Z.
    run_fp 40%nat [0x878cc%Z; 0x8459c%Z] noscr true.
    call_canon 368%Z HADM HCI 0x8457c%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep =>
              apply (out4 I' R' M' ic mc HADM' HCI'); kreg Hkeep (23%bv:reg)).
  Qed.


  (* [comment removed for export] *)
  Lemma out2 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 23 = Z_to_bv 64 1 ->
    getr R 9 = Z_to_bv 64 (a + 300) -> getr R 24 = Z_to_bv 64 (SB + (a + 300) / 8) -> getr R 18 = Z_to_bv 64 (a + 304) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84534) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI H23 H9 H24 H18. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    pkg_cell HADM 300%Z 3%Z C3.
    pin_s1 HR H9 300%Z. pin_sh HR (24%bv:reg) H24 300%Z 37%Z. pin_ak HR (18%bv:reg) H18 304%Z.
    run_fp 40%nat [0x878cc%Z; 0x8459c%Z] noscr true.
    call_canon 336%Z HADM HCI 0x84558%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep =>
              apply (out3 I' R' M' ic mc HADM' HCI'); [kreg Hkeep (23%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (24%bv:reg) | kreg Hkeep (18%bv:reg)]).
  Qed.

  (* [comment removed for export] *)
  Lemma out1 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 24 = Z_to_bv 64 SB ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84508) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI H24. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    pkg_cell HADM 300%Z 3%Z C3.
    pin_sb HR H24.
    run_fp 40%nat [0x878cc%Z; 0x8459c%Z] noscr true.
    call_canon 304%Z HADM HCI 0x84534%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep =>
              apply (out2 I' R' M' ic mc HADM' HCI'); [kreg Hkeep (23%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (24%bv:reg) | kreg Hkeep (18%bv:reg)]).
  Qed.

  (* [comment removed for export] *)
  Ltac relay L HADM HCI H24 :=
    let HADM1 := fresh "HADMr" in
    adm_now HADM HADM1;
    lazymatch type of HCI with chain_inv ?ic ?mc _ =>
    lazymatch goal with
    | HR : regs_ok _ _ _ |- runs_to _ (@mkst ?I1 ?R1 _ ?M1 _) _ =>
        apply (L I1 R1 M1 ic mc HADM1); [exact HCI | regv HR (24%bv:reg); first [exact H24 | reflexivity]]
    end end.

  (* [comment removed for export] *)
  Lemma mat3 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> mc = 3%Z -> getr R 24 = Z_to_bv 64 SB ->
    getr R 9 = Z_to_bv 64 (a + 296) -> getr R 19 = Z_to_bv 64 (SB + (a + 296) / 8) -> getr R 18 = Z_to_bv 64 (a + 152) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x844e4) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI Hmc3 H24 H9 H19 H18. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid). rewrite Hmc3 in C2.
    pkg_cell HADM 296%Z 3%Z C2.
    pin_sb HR H24. pin_s1 HR H9 296%Z. pin_sh HR (19%bv:reg) H19 296%Z 37%Z. pin_ak HR (18%bv:reg) H18 152%Z.
    run_fp 40%nat [0x878cc%Z; 0x84508%Z] noscr true.
    call_canon 216%Z HADM HCI 0x84508%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (out1 I' R' M' ic mc HADM' HCI'); kreg Hkeep (24%bv:reg)).
  Qed.

  (* [comment removed for export] *)
  Lemma mat2 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> mc = 3%Z -> getr R 24 = Z_to_bv 64 SB ->
    getr R 9 = Z_to_bv 64 (a + 296) -> getr R 19 = Z_to_bv 64 (SB + (a + 296) / 8) -> getr R 18 = Z_to_bv 64 (a + 152) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x844c0) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI Hmc3 H24 H9 H19 H18. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid). rewrite Hmc3 in C2.
    pkg_cell HADM 296%Z 3%Z C2.
    pin_sb HR H24. pin_s1 HR H9 296%Z. pin_sh HR (19%bv:reg) H19 296%Z 37%Z. pin_ak HR (18%bv:reg) H18 152%Z.
    run_fp 40%nat [0x878cc%Z; 0x84508%Z] noscr true.
    call_canon 184%Z HADM HCI 0x844e4%Z
      ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (mat3 I' R' M' ic mc HADM' HCI' Hmc3);
              [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (19%bv:reg) | kreg Hkeep (18%bv:reg)]).
  Qed.

  (* [comment removed for export] *)
  Lemma mat1 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 24 = Z_to_bv 64 SB ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84498) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI H24. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    destruct Hmc as [Hmc0 | Hmc3].
    - rewrite Hmc0 in C2. pkg_cell HADM 296%Z 0%Z C2. pin_sb HR H24.
      run_fp 40%nat [0x84508%Z; 0x878cc%Z] noscr true.
      relay out1 HADM HCI H24.
    - rewrite Hmc3 in C2. pkg_cell HADM 296%Z 3%Z C2. pin_sb HR H24.
      run_fp 40%nat [0x84508%Z; 0x878cc%Z] noscr true.
      call_canon 152%Z HADM HCI 0x844c0%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (mat2 I' R' M' ic mc HADM' HCI' Hmc3);
              [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (19%bv:reg) | kreg Hkeep (18%bv:reg)]).
  Qed.

  (* [comment removed for export] *)
  Lemma in4 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> (3 <= ic)%Z -> getr R 24 = Z_to_bv 64 SB ->
    getr R 9 = Z_to_bv 64 (a + 144) -> getr R 18 = Z_to_bv 64 (SB + (a + 144) / 8) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84474) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI Hic3 H24 H9 H18. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | Hc]; rewrite Hc in C1.
    - pkg_cell HADM 144%Z 3%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      relay mat1 HADM HCI H24.
    - pkg_cell HADM 144%Z 4%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      call_canon 96%Z HADM HCI 0x84498%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (mat1 I' R' M' ic mc HADM' HCI'); kreg Hkeep (24%bv:reg)).
  Qed.

  (* [comment removed for export] *)
  Lemma in3 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> (2 <= ic)%Z -> getr R 24 = Z_to_bv 64 SB ->
    getr R 9 = Z_to_bv 64 (a + 144) -> getr R 18 = Z_to_bv 64 (SB + (a + 144) / 8) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84450) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI Hic2 H24 H9 H18. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 2%Z \/ ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | [Hc | Hc]]; rewrite Hc in C1.
    - pkg_cell HADM 144%Z 2%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      relay mat1 HADM HCI H24.
    - pkg_cell HADM 144%Z 3%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      call_canon 64%Z HADM HCI 0x84474%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in4 I' R' M' ic mc HADM' HCI' ltac:(lia)); [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (18%bv:reg)]).
    - pkg_cell HADM 144%Z 4%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      call_canon 64%Z HADM HCI 0x84474%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in4 I' R' M' ic mc HADM' HCI' ltac:(lia)); [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (18%bv:reg)]).
  Qed.

  (* [comment removed for export] *)
  Lemma in2 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> (1 <= ic)%Z -> getr R 24 = Z_to_bv 64 SB ->
    getr R 9 = Z_to_bv 64 (a + 144) -> getr R 18 = Z_to_bv 64 (SB + (a + 144) / 8) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x8442c) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI Hic1 H24 H9 H18. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 1%Z \/ ic = 2%Z \/ ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | [Hc | [Hc | Hc]]]; rewrite Hc in C1.
    - pkg_cell HADM 144%Z 1%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      relay mat1 HADM HCI H24.
    - pkg_cell HADM 144%Z 2%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      call_canon 32%Z HADM HCI 0x84450%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in3 I' R' M' ic mc HADM' HCI' ltac:(lia)); [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (18%bv:reg)]).
    - pkg_cell HADM 144%Z 3%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      call_canon 32%Z HADM HCI 0x84450%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in3 I' R' M' ic mc HADM' HCI' ltac:(lia)); [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (18%bv:reg)]).
    - pkg_cell HADM 144%Z 4%Z C1. pin_sb HR H24. pin_s1 HR H9 144%Z. pin_sh HR (18%bv:reg) H18 144%Z 18%Z.
      run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true.
      call_canon 32%Z HADM HCI 0x84450%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in3 I' R' M' ic mc HADM' HCI' ltac:(lia)); [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (18%bv:reg)]).
  Qed.

  (* [comment removed for export] *)
  Lemma in0 : forall (FPI : FPState) R M ic mc,
    adm FPI R M -> chain_inv ic mc M -> getr R 24 = Z_to_bv 64 SB ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x84408) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc HADM HCI H24. adm_facts HADM.
    pose proof HCI as (C1 & C2 & C3 & Hic & Hmc & Hall & Hgrid).
    assert (Hc : ic = 0%Z \/ ic = 1%Z \/ ic = 2%Z \/ ic = 3%Z \/ ic = 4%Z) by lia.
    destruct Hc as [Hc | [Hc | [Hc | [Hc | Hc]]]]; rewrite Hc in C1;
    [ pkg_cell HADM 144%Z 0%Z C1 | pkg_cell HADM 144%Z 1%Z C1 | pkg_cell HADM 144%Z 2%Z C1
    | pkg_cell HADM 144%Z 3%Z C1 | pkg_cell HADM 144%Z 4%Z C1 ]; pin_sb HR H24;
    run_fp 40%nat [0x84498%Z; 0x878cc%Z] noscr true;
    [ relay mat1 HADM HCI H24 | .. ];
    call_canon 0%Z HADM HCI 0x8442c%Z
        ltac:(fun I' R' M' HADM' HCI' Hkeep => apply (in2 I' R' M' ic mc HADM' HCI' ltac:(lia)); [kreg Hkeep (24%bv:reg) | kreg Hkeep (9%bv:reg) | kreg Hkeep (18%bv:reg)]).
  Qed.

  (* [comment removed for export] *)
  Lemma okk : forall (FPI : FPState) R M ic mc (r : Z),
    adm FPI R M -> getr R 24 = Z_to_bv 64 SB -> getr R 10 = Z_to_bv 64 r ->
    (r = 0%Z \/ (r = 1%Z /\ chain_inv ic mc M)) ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x843fc) M rom) Qpost.
  Proof using ceil FPI0 regs0 mem0 rom ret data len bs sp T A pcs fs ch Hret HPRE Hcanon.
    intros FPI R M ic mc r HADM H24 H10 Hr. adm_facts HADM.
    destruct Hr as [-> | [-> HCI]].
    - pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 0%Z) by (cbn [edenot]; exact H10).
      run_fp 6%nat [0x84598%Z; 0x84408%Z] noscr true.
      adm_now HADM HADM1. apply (failk _ _ _ HADM1).
    - pkg HADM (@nil word) (@nil kentry) ltac:(constructor).
      pin_reg HR (10%bv:reg) (ELit 1%Z) by (cbn [edenot]; exact H10).
      run_fp 6%nat [0x84598%Z; 0x84408%Z] noscr true.
      adm_now HADM HADM1. apply (in0 _ _ _ ic mc HADM1); [exact HCI | regv HR (24%bv:reg); first [exact H24 | reflexivity]].
  Qed.
End RA.
