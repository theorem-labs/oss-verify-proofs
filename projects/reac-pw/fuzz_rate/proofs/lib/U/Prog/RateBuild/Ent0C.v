(** ent_build's kind 0 in the UBSan image (ent_headamp_key, pod.h:224-262), the making of ch (pod.h:236-249), from
    0x13ca4 (and 0x13ac4, the input used up before c) to the cut 0x13b64 ([Ent0Mid.case0_mid_at], a premise here).
    c > 199 takes odd_ch[c % 14] (0x13cac: c % 14 by the multiplier at 0x104d8, the .data.rel.ro table at 0x1ed10 and
    its UBSan bound check (not taken), strlen, memcpy of the text and its NUL into ch[24] at sp + 0x170, |r'| kept in
    s9 across the calls); else the decimal digits of c % 64 (0x13ae0: at most two turns of the digit loop into r[4] at
    sp + 0x150, its UBSan check on k = 4 not taken, the reverse copy into ch, the UBSan check on ch + n (not taken) and
    the NUL). The form is reac-pw/fuzz_role's U/Prog/RoleBuild/Ent0C.v,
    re-walked on rate's code.

    Also here, shared with Ent0.v: the model's key, and the stores into [sp + 0x150, sp + 0x1e8). *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Lib Require Import Tac Image.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog Require Import SlotInv LLVMFuzzerTestOneInput_c memcpy_c
  strlen_c.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Pod Require Import Cursor Tables Model Layout RateImg.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.U.Prog.RateBuild Require Import EntCut EntFacts EntRo Ent0Mid.
Import ListNotations.
Open Scope Z_scope.

(** ** The model's key *)
Definition chsel (c : Z) : list byte := if c <? 200 then dec64 (c mod 64) else nth (Z.to_nat (c mod 14)) odd_ch [].
Definition key0 (c p : Z) : list byte :=
  join_parts [HPFX; chsel c; if Z.testbit p 7 then [] else DOT; nth (Z.to_nat (p mod 8)) param []].

(** ** Bytes *)
Lemma le1_z : forall x, le1 (Z_to_bv 64 x) = [Z_to_bv 8 x].
Proof.
  intros x. unfold le1. cbn [Z_to_le_bytes]. f_equal. apply Z_to_bv8_mod.
  rewrite unsigned_lit_wrap. apply mod_mod8_of_modw. lia.
Qed.

Lemma byte_self0 : forall b : byte, Z_to_bv 8 (bv_unsigned b) = b.
Proof. intros b. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma le1_zb : forall b : byte, le1 (zxb b) = [b].
Proof. intros b. unfold zxb. rewrite le1_z. f_equal. apply byte_self0. Qed.

Lemma digit_nz : forall d, 0 <= d < 10 -> digit d <> NUL.
Proof.
  intros d Hd E. apply (f_equal bv_unsigned) in E. unfold digit, NUL in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 8) with 256 in E.
  rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma dec64_nonul : forall v, 0 <= v < 64 -> ~ In NUL (dec64 v).
Proof.
  intros v Hv. unfold dec64. destruct (v <? 10) eqn:E.
  - apply Z.ltb_lt in E. intros [X|[]]. exact (digit_nz v ltac:(lia) X).
  - apply Z.ltb_ge in E. pose proof (Z.mod_pos_bound v 10 ltac:(lia)).
    assert (0 <= v / 10 < 10) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    intros [X|[X|[]]]; [exact (digit_nz (v / 10) ltac:(lia) X) | exact (digit_nz (v mod 10) ltac:(lia) X)].
Qed.

(** ch and its NUL from the byte stores of the reverse copy. *)
Lemma ch1_bytes : forall m1 A a0 a1 d, bytes_at rsegs m1 a0 [d] -> bytes_at rsegs m1 a1 [NUL] ->
  a0 = A -> a1 = A + 1 -> bytes_at rsegs m1 A ([d] ++ [NUL]).
Proof.
  intros m1 A a0 a1 d H0 H1 -> ->. apply bytes_at_app. split; [exact H0|].
  cbn [length]. replace (A + Z.of_nat 1) with (A + 1) by lia. exact H1.
Qed.

Lemma ch2_bytes : forall m1 A a0 a1 a2 d0 d1, bytes_at rsegs m1 a0 [d0] -> bytes_at rsegs m1 a1 [d1] ->
  bytes_at rsegs m1 a2 [NUL] -> a0 = A -> a1 = A + 1 -> a2 = A + 2 -> bytes_at rsegs m1 A ([d0; d1] ++ [NUL]).
Proof.
  intros m1 A a0 a1 a2 d0 d1 H0 H1 H2 -> -> ->.
  change ([d0; d1] ++ [NUL]) with ([d0] ++ ([d1] ++ [NUL])).
  apply bytes_at_app. split; [exact H0|]. cbn [length].
  apply bytes_at_app. split.
  - replace (A + Z.of_nat 1) with (A + 1) by lia. exact H1.
  - cbn [length]. replace (A + Z.of_nat 1 + Z.of_nat 1) with (A + 2) by lia. exact H2.
Qed.

(** ** The odd_ch texts and their table *)
Definition odd_b (i : nat) : bool :=
  rostr_ok (nth i (pa_odd_s rate_ubsan_addrs) 0) (nth i odd_ch []) && (length (nth i odd_ch []) <=? 21)%nat.

Lemma odd_strs : forallb odd_b (seq 0 14) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma odd_str : forall i, (i < 14)%nat ->
  rostr_ok (nth i (pa_odd_s rate_ubsan_addrs) 0) (nth i odd_ch []) = true /\ (length (nth i odd_ch []) <= 21)%nat.
Proof.
  intros i Hi. pose proof odd_strs as H. rewrite forallb_forall in H.
  specialize (H i ltac:(apply in_seq; lia)). unfold odd_b in H. apply andb_prop in H as [H1 H2].
  split; [exact H1 | apply Nat.leb_le; exact H2].
Qed.

Lemma odd_tbl : relro8_ok 0x1ed10 (pa_odd_s rate_ubsan_addrs) = true.
Proof. vm_compute. reflexivity. Qed.

(** ** Walk tactics *)
(** [zcheck x Hx] proves L = R where x : Z (Hx : 0 <= x < 256) is the only variable: all 256 values checked. *)
Ltac zcheck x Hx :=
  cbv delta [zxb]; unfold bv_signed; rewrite ?Z_to_bv_unsigned;
  clear - Hx; revert x Hx; first [apply byte_check | apply byte_checkb]; vm_compute; reflexivity.

Ltac lenz := rewrite ?length_app, ?length_le1, ?length_le4, ?length_le8; cbn [length].

(** Carry the bytes_at facts of the memory m1 across a store of bs at a (dropping those it overwrites). *)
Ltac keepw m1 a bs :=
  repeat match goal with
  | H : bytes_at rsegs m1 ?A ?l |- _ =>
      first [ apply (bytes_at_write_other rsegs m1 a bs A l) in H;
              [ change (wa a) with (Z_to_bv 64 a) in H | lia | lenz; unfold FRAME_LOCALS in *; lia
              | lenz; unfold FRAME_LOCALS in *; lia ]
            | clear H ]
  end.

(** A store of n bytes at a (a Z expression) into [sp + 0x150, sp + 0x1e8): MemC carried, the other bytes_at
    facts carried, the stored bytes as a fact ST, the memory named again. *)
Ltac hst HE MC a n :=
  lazymatch type of MC with MemC ?sp0 ?m0 ?lo0 ?m1 ?t ?sz ?bd =>
    let HS := fresh "HS" in
    assert (HS : store_ok rsegs m1 (wa a) n = true)
      by (apply (MemC_store_ok _ _ _ _ _ _ HE m1 t sz bd); [exact MC | lia | unfold FRAME_LOCALS; lia]);
    step; clear HS;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem m1 (Z_to_bv 64 ?a') ?bs) _) =>
      let MC2 := fresh "MCn" in
      pose proof (MemC_st_hi _ _ _ _ _ _ HE m1 t sz bd a' bs MC ltac:(lia)
                    ltac:(lenz; unfold FRAME_LOCALS in *; lia)) as MC2;
      keepw m1 a' bs;
      let ST := fresh "ST" in
      assert (ST : bytes_at rsegs (write_to_mem m1 (Z_to_bv 64 a') bs) a' bs)
        by (apply bytes_at_write_same; lenz; unfold FRAME_LOCALS in *; lia);
      clear MC; rename MC2 into MC; name_mem
    end
  end.

Section Ch.
Variables (sp gp tp s3 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (r : list byte)
          (src pp lo : Z).
Hypothesis HE : ent_pre sp m r src pp lo.
Hypothesis MCPY : memcpy_contract.
Hypothesis STRL : strlen_contract.
Hypothesis MID : case0_mid_at sp gp tp s3 F fc m r src pp lo.

Local Abbreviation QE := (QJ sp gp tp s3 F fc m r src pp lo (ent_build r)).

(** 0x13ae0: the digits of v = c % 64 into r[] (one turn of the loop when v < 10, two else), reversed into ch,
    the NUL after them; then the cut 0x13b64. *)
Lemma digits_ok : forall (c p : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1,
  0 <= c < 256 -> 0 <= p < 256 ->
  ent_build r = (ent_text (join_parts [HPFX; dec64 (c mod 64); if Z.testbit p 7 then [] else DOT;
                                       nth (Z.to_nat (p mod 8)) param []]) true, r') ->
  a0 = Z_to_bv 64 c -> a7 = Z_to_bv 64 (bv_unsigned sp + 336) -> t0 = Z_to_bv 64 9 ->
  t1 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s10 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s8 = Z_to_bv 64 p ->
  s6 = Z_to_bv 64 (bv_unsigned sp + 0x170) ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ae0) fc None m1 (seg_rom rsegs)).
Proof.
  intros c p r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hc Hp Eb -> -> -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13ae0 mv a1,zero; andi a4,a0,0x3f; addi a5,sp,0x150 *)
  do 3 step.
  match goal with |- context [Z.land ?X 63] => replace (Z.land X 63) with (c mod 64) by (zcheck c Hc) end.
  remember (c mod 64) as v eqn:Ev.
  assert (Hv : 0 <= v < 64) by (subst v; apply Z.mod_pos_bound; lia).
  assert (Hv' : 0 <= v < 256) by lia.
  try rewrite <- Ev in Eb.
  (* 0x13aec beq a1,s1: k = 4 traps, not taken *)
  step. brf.
  (* 0x13af0 .. 0x13b18: r[0] = '0' + v % 10, a4 = v / 10 *)
  do 11 step.
  match goal with |- context [Z.lor ?E 48] =>
    replace (Z.lor E 48) with (48 + v mod 10) by (zcheck v Hv') end.
  match goal with |- context [Z.shiftr ?E 35] =>
    replace (Z.shiftr E 35) with (v / 10) by (zcheck v Hv') end.
  (* 0x13b1c sb a6,0(a5) *)
  hst HE MC (bv_unsigned sp + 336) 1%nat. rename ST into D0. rewrite le1_z in D0.
  (* 0x13b20 addi a5,a0,1; bltu t0,a3 (another digit when v > 9) *)
  do 2 step.
  destruct (Z_le_gt_dec v 9) as [V1|V2].
  - (* one digit *)
    brf.
    (* 0x13b28 addi a3,sp,0x170; add a2,a2,a3; addi a2,a2,1 *)
    do 3 step.
    (* 0x13b34 lbu a4,0(a0): r[0]; sb a4,0(a3): ch[0] *)
    pose proof (bytes_at_byte _ _ _ 0 D0 ltac:(cbn [length]; lia)) as HR. cbn [nth] in HR.
    step. clear HR.
    hst HE MC (bv_unsigned sp + 368) 1%nat. rename ST into C0. rewrite le1_zb in C0.
    (* addi a3,a3,1; addi a0,a0,-1; bne a3,a2 (done) *)
    do 3 step. brf.
    (* 0x13b48 slli a0,a1,32; srli a0,a0,32; ld a1,0x80(sp); bltu a1,a0 (ch + n overflows: not taken) *)
    do 2 step.
    pose proof (MemC_c80 sp m r src pp lo HE _ _ _ _ MC) as R80. step. clear R80.
    step. brf.
    (* 0x13b58 addi a1,sp,0x170; add a0,a1,a0; sb zero,0(a0): ch[1] = 0 *)
    do 2 step.
    hst HE MC (bv_unsigned sp + 369) 1%nat. rename ST into C1. rewrite ?w0_lit, ?le1_z in C1.
    rewrite (Z.mod_small v 10) in C0 by lia.
    eapply MID with (p := p) (ch := dec64 v) (r' := r');
      [ exact Eb | exact Hp | reflexivity | apply dec64_nonul; lia | pose proof (dec64_len v); lia
      | | reflexivity | reflexivity | reflexivity | exact MC ].
    unfold dec64, digit. replace (v <? 10) with true by (symmetry; apply Z.ltb_lt; lia).
    eapply ch1_bytes; [exact C0 | exact C1 | lia | lia].
  - (* two digits: the loop's second turn *)
    brt.
    (* 0x13aec beq a1,s1 (trap) *)
    step. brf.
    do 11 step.
    match goal with |- context [Z.lor ?E 48] =>
      replace (Z.lor E 48) with (48 + (v / 10) mod 10) by (zcheck v Hv') end.
    match goal with |- context [Z.shiftr ?E 35] =>
      replace (Z.shiftr E 35) with (v / 10 / 10) by (zcheck v Hv') end.
    (* 0x13b1c sb a6,0(a5): r[1] *)
    hst HE MC (bv_unsigned sp + 337) 1%nat. rename ST into D1. rewrite le1_z in D1.
    (* addi a5,a0,1; bltu t0,a3 (done) *)
    do 2 step. brf.
    (* 0x13b28 addi a3,sp,0x170; add a2,a2,a3; addi a2,a2,1 *)
    do 3 step.
    (* r[1] to ch[0] *)
    pose proof (bytes_at_byte _ _ _ 0 D1 ltac:(cbn [length]; lia)) as HR. cbn [nth] in HR.
    step. clear HR.
    hst HE MC (bv_unsigned sp + 368) 1%nat. rename ST into C0. rewrite le1_zb in C0.
    do 3 step. brt.
    (* r[0] to ch[1] *)
    pose proof (bytes_at_byte _ _ _ 0 D0 ltac:(cbn [length]; lia)) as HR. cbn [nth] in HR.
    step. clear HR.
    hst HE MC (bv_unsigned sp + 369) 1%nat. rename ST into C1. rewrite le1_zb in C1.
    do 3 step. brf.
    (* 0x13b48 .. 0x13b54: the check on ch + n *)
    do 2 step.
    pose proof (MemC_c80 sp m r src pp lo HE _ _ _ _ MC) as R80. step. clear R80.
    step. brf.
    (* ch[2] = 0 *)
    do 2 step.
    hst HE MC (bv_unsigned sp + 370) 1%nat. rename ST into C2. rewrite ?w0_lit, ?le1_z in C2.
    rewrite (Z.mod_small (v / 10) 10) in C0 by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    eapply MID with (p := p) (ch := dec64 v) (r' := r');
      [ exact Eb | exact Hp | reflexivity | apply dec64_nonul; lia | pose proof (dec64_len v); lia
      | | reflexivity | reflexivity | reflexivity | exact MC ].
    unfold dec64, digit. replace (v <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
    eapply ch2_bytes; [exact C0 | exact C1 | exact C2 | lia | lia | lia].
Qed.

(** 0x13cac (c > 199): c % 14 by multiply, odd_ch[c % 14]'s pointer, |r'| to s9, strlen, memcpy(ch, o, l + 1),
    |r'| back to t1; then the cut 0x13b64. *)
Lemma odd_ok : forall (c p : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1,
  200 <= c < 256 -> 0 <= p < 256 ->
  ent_build r = (ent_text (join_parts [HPFX; nth (Z.to_nat (c mod 14)) odd_ch []; if Z.testbit p 7 then [] else DOT;
                                       nth (Z.to_nat (p mod 8)) param []]) true, r') ->
  a0 = Z_to_bv 64 c -> t1 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s10 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s8 = Z_to_bv 64 p ->
  s6 = Z_to_bv 64 (bv_unsigned sp + 0x170) ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13cac) fc None m1 (seg_rom rsegs)).
Proof.
  intros c p r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hc Hp Eb -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  assert (Hc' : 0 <= c < 256) by lia.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI.
  (* 0x13cac auipc a1; ld a1,-0x7d4(a1) (the multiplier at 0x104d8); mulhu a1,a0,a1; slli a2,a1,4; slli a1,a1,1;
     sub a2,a1,a2; auipc a1; addi a1,a1,0x4c; add a0,a0,a2; slli a0,a0,3 *)
  do 10 step.
  match goal with |- context [Z.shiftl ?E 3] =>
    replace (Z.shiftl E 3) with (8 * (c mod 14)) by (zcheck c Hc') end.
  clear MI.
  (* 0x13cd4 not a2,a1; bltu a2,a0 (the table index overflows: not taken) *)
  do 2 step. brf.
  (* 0x13cdc add a0,a1,a0; ld s7,0(a0): odd_ch[c % 14]'s pointer *)
  step.
  assert (HR : ov_read_bytes rsegs m1 (wa (0x1ed10 + 8 * Z.of_nat (Z.to_nat (c mod 14)))) 8
               = Some (le8 (Z_to_bv 64 (nth (Z.to_nat (c mod 14)) (pa_odd_s rate_ubsan_addrs) 0)))).
  { apply relro8_read; [exact odd_tbl | | lia | | ].
    - change (length (pa_odd_s rate_ubsan_addrs)) with 14%nat. lia.
    - change (length (pa_odd_s rate_ubsan_addrs)) with 14%nat. lia.
    - intros x Hx. change (length (pa_odd_s rate_ubsan_addrs)) with 14%nat in Hx.
      apply (MemC_relro sp m r src pp lo HE m1 _ _ _ x MC). unfold RELRO_TBL, RELRO_TBL_END. lia. }
  step. clear HR.
  pose proof (odd_str (Z.to_nat (c mod 14)) ltac:(lia)) as (Hro & Ls).
  revert Eb Hro Ls.
  generalize (nth (Z.to_nat (c mod 14)) odd_ch []) as s.
  generalize (nth (Z.to_nat (c mod 14)) (pa_odd_s rate_ubsan_addrs) 0) as o.
  intros o s Eb Hro Ls.
  pose proof (MemC_mem_inv _ _ _ _ _ _ _ MC) as MI.
  destruct (rostr_bytes m1 o s MI Hro) as (SB & NN & SL & P0 & P1 & _).
  (* 0x13ce4 mv a0,s7; mv s9,t1; jal strlen *)
  do 3 step.
  eapply evt_cut.
  { eapply STRL with (str := s) (slack := img_slack o s).
    - rewrite unsigned_lit by lia. exact SB.
    - exact NN.
    - rewrite unsigned_lit by lia. exact SL.
    - exact MI. }
  intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 &
              E & MU2 & WM2 & MI2 & SB2).
  subst ms'. rewrite unsigned_lit in SB2 by lia.
  pose proof (MemC_call_nil _ _ _ _ _ _ _ _ MC MU2 WM2 MI2) as MC2.
  clear MC MU2 WM2 MI SB.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13cf0 addi a2,a0,1; addi a0,sp,0x170; mv a1,s7; jal memcpy *)
  do 4 step.
  destruct (MemC_cells sp m r src pp lo HE m2 _ _ _ (bv_unsigned sp + 368) (S (length s)) MC2
              ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as (jk & Ljk & CJ).
  replace (s ++ Z_to_bv 8 0 :: img_slack o s) with ((s ++ [NUL]) ++ img_slack o s) in SB2
    by (rewrite <- app_assoc; reflexivity).
  apply bytes_at_app in SB2 as [SBs _].
  eapply evt_cut.
  { eapply MCPY with (src := s ++ [NUL]) (junk := jk).
    - rewrite unsigned_lit by lia. exact SBs.
    - rewrite unsigned_lit by lia. rewrite length_app. cbn [length]. lia.
    - rewrite !unsigned_lit by lia. replace (Z.to_nat (Z.of_nat (length s) + 1)) with (S (length s)) by lia.
      exact CJ.
    - rewrite !unsigned_lit by lia.
      destruct (ro_apart sp m r src pp lo HE o s (bv_unsigned sp + 368) (Z.of_nat (length s) + 1) Hro
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as [X|X]; [left | right]; lia.
    - exact MI2. }
  intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & m3 &
              E3 & MU3 & WM3 & MI3 & RC3 & _).
  subst ms'. rewrite !unsigned_lit in MU3, RC3 by lia.
  apply rw_CB_bytes in RC3 as [B3 L3].
  pose proof (MemC_call_hi sp m r src pp lo HE m2 m3 _ _ _ _ _ _ MC2 MU3 WM3 MI3 B3
                ltac:(rewrite L3; lia) ltac:(lia) ltac:(unfold FRAME_LOCALS; lia)) as MC3.
  clear MC2 MU3 WM3 MI3 CJ SBs MI2.
  rewrite ret_pc_even by (lia || reflexivity).
  (* 0x13d00 mv t1,s9; j 0x13b64 *)
  do 2 step.
  eapply MID with (p := p) (ch := s) (r' := r');
    [ exact Eb | exact Hp | reflexivity | exact NN | exact Ls | exact B3 | reflexivity | reflexivity | reflexivity
    | exact MC3 ].
Qed.

(** 0x13ca4: c <= 199 to the digits (0x13ae0), else to odd_ch (0x13cac). *)
Lemma c_ok : forall (c p : Z) (r' : list byte)
    (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1,
  0 <= c < 256 -> 0 <= p < 256 ->
  ent_build r = (ent_text (key0 c p) true, r') ->
  a0 = Z_to_bv 64 c -> a7 = Z_to_bv 64 (bv_unsigned sp + 336) -> t0 = Z_to_bv 64 9 ->
  t1 = Z_to_bv 64 (Z.of_nat (length r')) ->
  s10 = Z_to_bv 64 (src + Z.of_nat (length r) - Z.of_nat (length r')) -> s8 = Z_to_bv 64 p ->
  s6 = Z_to_bv 64 (bv_unsigned sp + 0x170) ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ca4) fc None m1 (seg_rom rsegs)).
Proof.
  intros c p r' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1
    Hc Hp Eb -> -> -> -> -> -> -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  unfold key0, chsel in Eb.
  (* 0x13ca4 addi a1,zero,0xc7; bgeu a1,a0 *)
  do 2 step.
  destruct (Z_lt_ge_dec 199 c) as [H|H].
  - brf. replace (c <? 200) with false in Eb by (symmetry; apply Z.ltb_ge; lia).
    eapply (odd_ok c p r'); [lia | exact Hp | exact Eb | reflexivity | reflexivity | reflexivity | reflexivity
                            | reflexivity | exact MC].
  - brt. replace (c <? 200) with true in Eb by (symmetry; apply Z.ltb_lt; lia).
    eapply (digits_ok c p r'); [exact Hc | exact Hp | exact Eb | reflexivity | reflexivity | reflexivity
                               | reflexivity | reflexivity | reflexivity | reflexivity | exact MC].
Qed.

(** 0x13ac4: the input used up before c (s9 = the cursor at its end): c = p = 0 (0x13ac4-0x13adc: s6 = ch's end,
    a7 = r[], t0 = 9, t1 = 0, s8 = p = 0, a0 = c = 0, s10 = s9), then the digits of 0. Reached from the head with
    r = [] (s9 = src) and from 0x13ac0 with r = [kind] (s9 = src + 1). *)
Lemma nil_ok : forall (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) m1,
  ent_build r = (ent_text (key0 0 0) true, []) ->
  s9 = Z_to_bv 64 (src + Z.of_nat (length r)) ->
  MemC sp m lo m1 (Z_to_bv 64 0) (Z_to_bv 64 0) (zeros 96) ->
  evt rsegs QE
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (bv_unsigned sp + 0x188)) (Z_to_bv 64 4) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 95) s3 (Z_to_bv 64 (0xcccccccd * 2^32)) (Z_to_bv 64 10) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13ac4) fc None m1 (seg_rom rsegs)).
Proof.
  intros ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 m1 Eb -> MC.
  pose proof (ep_range sp m r src pp lo HE) as R.
  (* 0x13ac4 addi s6,sp,0x170; addi a7,sp,0x150; addi t0,zero,9; mv t1,zero; mv s8,zero; mv a0,zero; mv s10,s9 *)
  do 7 step.
  eapply (digits_ok 0 0 []);
    [ lia | lia | rewrite Eb; reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
    | f_equal; cbn [length]; lia | reflexivity | reflexivity | exact MC ].
Qed.

End Ch.
