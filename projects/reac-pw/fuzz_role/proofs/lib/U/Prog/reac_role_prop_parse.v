(** reac_role_prop_parse (UBSan image, 0x14648, 183 instructions) against reac_role_prop_parse_contract
    (U/Prog/reac_role_prop_parse_c.v), with strcmp_contract (U/Prog/strcmp_c.v) as premise. The plain walk's shape
    (Prog/reac_role_prop_parse.v), with the UBSan differences: the prologue runs before the NULL test, so a NULL
    argument returns -1 through the frame and the epilogue (0x148ec, 0x148f0: the answer is in a1); the find loop at
    0x146d0 keeps the object body in a0; the Struct walk at 0x1475c keeps the key in a0 and vs - 8, the body and its
    end in s4, s5, s6; the value read is at 0x147f8. Each of the ten trap branches (to the `unimp` at 0x14920) is shown
    not taken from the walk's facts: P, the found prop and the role cell are 4-aligned and nonzero, the key string's
    last byte address does not wrap, and the double d lies in [-2^31, 2^31) before the cast bounds and the `r--`
    check (Prog/ParseFP.v's rfn_hw_above, rfn_hw_below, rfn_hw_t_range). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Import Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Cells Step Image FP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Tables Model Accessors Spa Nearest Role.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Prog Require Import ParseFP.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.U.Prog Require Import strcmp_c reac_role_prop_parse_c.
Import ListNotations.
Open Scope Z_scope.

(** * The model, one pass at a time *)
Lemma find_prop_step : forall bs size key res n,
  find_prop bs size key res (S n) =
  if prop_is_inside bs 8 size res then
    if u32_at bs res =? key then Some res
    else find_prop bs size key (res + round_up8 (16 + u32_at bs (res + 8))) n
  else None.
Proof. reflexivity. Qed.

(** The answer from the walk's position: the pods of the Struct body [body] of [size] bytes from offset c, with the
    key slot k (None: open; Some k': the key k' waits for its value). *)
Definition walk_res (bs : list byte) (body size c : Z) (n : nat) (k : option (list byte)) : option role * Z :=
  role_of_pairs spa_role_value (pairs_by spa_get_string (map (child_at bs) (struct_children bs body size c n)) k).

Lemma walk_res_step : forall bs body size c n k,
  walk_res bs body size c (S n) k =
  if pod_is_inside bs body size c then
    match k with
    | None => walk_res bs body size (c + round_up8 (8 + u32_at bs c)) n (spa_get_string (child_at bs c))
    | Some k' => if bytes_eqb k' ROLE_KEY then spa_role_value (child_at bs c)
                 else walk_res bs body size (c + round_up8 (8 + u32_at bs c)) n None
    end
  else (None, 0).
Proof.
  intros bs body size c n k. unfold walk_res. cbn [struct_children].
  destruct (pod_is_inside bs body size c); [|reflexivity].
  cbn [map]. destruct k as [k'|]; cbn [pairs_by]; [|reflexivity].
  unfold role_of_pairs at 1. cbn [find fst]. destruct (bytes_eqb k' ROLE_KEY); reflexivity.
Qed.

Lemma parse_model_not_props : forall bs, is_object_type bs POD_OBJECT_PROPS = false -> parse_model bs = (None, -1).
Proof. intros bs H. unfold parse_model, spa_view_of. rewrite H. reflexivity. Qed.

Lemma parse_model_no_params : forall bs, is_object_type bs POD_OBJECT_PROPS = true ->
  find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs) = None -> parse_model bs = (None, 0).
Proof. intros bs H E. unfold parse_model, spa_view_of. rewrite H, E. reflexivity. Qed.

Lemma parse_model_found : forall bs r, is_object_type bs POD_OBJECT_PROPS = true ->
  find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs) = Some r ->
  parse_model bs = if is_struct_at bs (r + 8)
                   then walk_res bs (r + 16) (u32_at bs (r + 8)) (r + 16) (length bs) None else (None, 0).
Proof.
  intros bs r H E. unfold parse_model, spa_view_of. rewrite H, E.
  destruct (is_struct_at bs (r + 8)); reflexivity.
Qed.

(** * The key text and the image *)
Lemma notin_nul_of_no_nul : forall l, no_nul l = true -> ~ In NUL l.
Proof.
  induction l as [|x l IH]; unfold no_nul; cbn [forallb In]; [tauto|]. intros H [E|E].
  - subst x. vm_compute in H. discriminate H.
  - apply andb_prop in H as [_ H]. exact (IH H E).
Qed.

Lemma ROLE_KEY_nonul : ~ In NUL ROLE_KEY.
Proof. apply notin_nul_of_no_nul. vm_compute. reflexivity. Qed.

Lemma ROLE_KEY_length : length ROLE_KEY = 13%nat.
Proof. vm_compute. reflexivity. Qed.

(** "reac.cfg.role" and its NUL at 0x1032e (.rodata). *)
Lemma lit_at : forall m, mem_inv rsegs m -> bytes_at rsegs m 0x1032e (ROLE_KEY ++ [NUL]).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI | lia | |].
  - change (length (ROLE_KEY ++ [NUL])) with 14%nat. lia.
  - apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

(** * The walk *)
Section W.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (mi : word -> option byte) (null : bool) (lo P Q : Z) (bs : list byte).
Hypothesis HARGS : role_args mi lo (bv_unsigned sp) P Q bs.
Hypothesis HSTK : stk rsegs mi lo (bv_unsigned sp).
Hypothesis HLO : lo + PARSE_FRAME <= bv_unsigned sp.
Hypothesis HNOROM : forall a, lo <= a < bv_unsigned sp -> seg_rom rsegs (wa a) = None.
Hypothesis HFRM : frm0 fc.
Hypothesis HMI : mem_inv rsegs mi.
Hypothesis HSTR : strcmp_contract.

(** The answer: -1 for a NULL argument, else parse_model of the pod bytes. *)
Definition RES : option role * Z := parse_res null bs.

(** The contract's post. *)
Definition Post (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (snd RES))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
    (forall k : bv 5, ~ (13 <= bv_unsigned k <= 15) -> Sem.reg_get F' k = Sem.reg_get F k) /\
    frm0 fc' /\
    role_mem mi m' (bv_unsigned sp) Q (fst RES) /\
    wmono rsegs mi m' /\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

(** The frame after the prologue: the saved registers at sp - 80 (the 8 bytes at sp - 80 are the float temp), the
    stack below it, memory changed only in the frame. *)
Definition frame (m : word -> option byte) : Prop :=
  (exists j, rw_cells rsegs m (bv_unsigned sp + -80)
               [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) /\
  stk rsegs m lo (bv_unsigned sp + -80) /\ munch [(bv_unsigned sp - PARSE_FRAME, bv_unsigned sp)] mi m /\
  wmono rsegs mi m /\ mem_inv rsegs m.

Lemma args_facts : 8 <= Z.of_nat (length bs) /\ u32_at bs 0 = Z.of_nat (length bs) - 8 /\ 0 < P /\
  P mod 16 = 0 /\ P + Z.of_nat (length bs) <= lo /\ Q mod 4 = 0 /\ bv_unsigned sp <= Q /\
  0 <= lo /\ bv_unsigned sp < 2^64 /\ lo + 80 <= bv_unsigned sp.
Proof.
  pose proof HARGS as (_ & H0 & H16 & H8 & HS & HPL & _ & HQ4 & HSQ).
  pose proof HSTK as (L0 & _ & _). pose proof (bv_unsigned_in_range 64 sp) as R.
  change (bv_modulus 64) with (2^64) in R. pose proof HLO as HL. unfold PARSE_FRAME in HL.
  repeat split; lia.
Qed.

(** The pod's bytes, in any memory the frame allows. *)
Lemma pod_at : forall m, frame m -> bytes_at rsegs m P bs.
Proof.
  intros m (_ & _ & MU & _ & _). pose proof HARGS as (HB & _).
  pose proof args_facts as (_ & _ & _ & _ & HPL & _ & _ & _ & _ & HL).
  eapply bytes_at_transport; [exact HB | exact MU |]. unfold PARSE_FRAME. cbn [disjoint_from].
  split; [lia | exact I].
Qed.

(** The role cell, writable in any memory the frame allows. *)
Lemma cell_wr : forall m, frame m -> wr_at rsegs m Q 4.
Proof.
  intros m (_ & _ & _ & WM & _). pose proof HARGS as (_ & _ & _ & _ & _ & _ & HW & _).
  exact (wr_at_transport rsegs mi m Q 4 HW WM).
Qed.

(** *** The words of the pod, the branch tests and the model steps *)
Lemma ua_res : null = false -> RES = parse_model bs.
Proof. intros H. unfold RES, parse_res. rewrite H. reflexivity. Qed.

Lemma ua_le_roundtrip : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb. pose proof (le_bytes_nonneg l) as Hl.
  rewrite (lor_low_shiftl (bv_unsigned b) (bytes_le_to_Z l) Hb Hl). f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap.
    replace (bv_modulus 8) with 256 by reflexivity.
    rewrite Z_mod_plus_full. apply Z.mod_small. exact Hb.
  - replace (Z.shiftr (bv_unsigned b + bytes_le_to_Z l * 256) 8) with (bytes_le_to_Z l); [exact IH|].
    rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 8) with 256 by reflexivity.
    rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma ua_u32 : forall o, 0 <= u32_at bs o < 2^32.
Proof. intros o. exact (rd32_range _). Qed.

(** The 4 bytes at offset o of the pod, read in any memory the frame allows. *)
Lemma ua_rd : forall m o, frame m -> 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (P + o)) 4%nat = Some (le4 (Z_to_bv 64 (u32_at bs o))).
Proof.
  intros m o FR H0 H4. pose proof (pod_at m FR) as B.
  replace (P + o) with (P + Z.of_nat (Z.to_nat o)) by lia.
  rewrite (bytes_at_ov_read rsegs m P bs (Z.to_nat o) 4 B ltac:(lia)).
  f_equal. unfold le4, u32_at, rd32.
  pose proof (rd32_range (skipn (Z.to_nat o) bs)) as R. unfold rd32 in R.
  rewrite unsigned_lit by lia.
  assert (L : length (firstn 4 (skipn (Z.to_nat o) bs)) = 4%nat)
    by (rewrite length_firstn, length_skipn; lia).
  pose proof (ua_le_roundtrip (firstn 4 (skipn (Z.to_nat o) bs))) as E. rewrite L in E. symmetry. exact E.
Qed.

(** A sign-extended word (lw) of the pod. *)
Lemma ua_hm32 : bv_half_modulus 32 = 2^31.
Proof. reflexivity. Qed.

Lemma ua_sx32 : forall v, 0 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. rewrite unsigned_lit by lia. rewrite bv_swrap_small; [reflexivity|].
  rewrite ua_hm32. lia.
Qed.

Lemma ua_wsx : forall v, 0 <= v < 2^32 -> bv_wrap 32 (bv_unsigned (sx32 (Z_to_bv 64 v))) = v.
Proof.
  intros v Hv. unfold sx32. rewrite Z_to_bv_unsigned, unsigned_lit by lia.
  unfold bv_swrap, bv_wrap. rewrite ua_hm32.
  replace (bv_modulus 32) with (2^32) by reflexivity. replace (bv_modulus 64) with (2^64) by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ua_srliw_sx : forall v, 0 <= v < 2^32 ->
  bv_swrap 32 (Z.shiftr (bv_wrap 32 (bv_unsigned (sx32 (Z_to_bv 64 v)))) 20) = v / 1048576.
Proof.
  intros v Hv. rewrite (ua_wsx v Hv). rewrite Z.shiftr_div_pow2 by lia. replace (2 ^ 20) with 1048576 by reflexivity.
  assert (0 <= v / 1048576 < 4096) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  apply bv_swrap_small. rewrite ua_hm32. lia.
Qed.

Lemma ua_sxmod : forall v, 0 <= v < 2^32 -> bv_unsigned (sx32 (Z_to_bv 64 v)) mod 4294967296 = v.
Proof.
  intros v Hv. pose proof (ua_wsx v Hv) as E. unfold bv_wrap in E.
  replace (bv_modulus 32) with 4294967296 in E by reflexivity. exact E.
Qed.

Lemma ua_eqb_sx : forall v k, 0 <= v < 2^32 -> 0 <= k < 2^31 ->
  bv_eqb (sx32 (Z_to_bv 64 v)) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb, sx32. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. rewrite ua_hm32.
  replace (bv_modulus 32) with (2^32) by reflexivity. replace (bv_modulus 64) with (2^64) by reflexivity.
  rewrite (Z.mod_small v (2^64)), (Z.mod_small k (2^64)) by lia.
  apply eq_true_iff_eq. rewrite !Z.eqb_eq. split; intros E; Z.div_mod_to_equations; lia.
Qed.

Lemma ua_land3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

(** SPA_ROUND_UP_N(16 + v, 8) as the code computes it ((v + 15) | 7, then + 1). *)
Lemma ua_ru : forall v, Z.lor (v + 15) 7 = round_up8 (16 + v) - 1.
Proof. intros v. unfold round_up8. replace (16 + v - 1) with (v + 15) by lia. lia. Qed.

Lemma ua_ru_facts : forall v, 0 <= v -> 16 + v <= round_up8 (16 + v) <= 23 + v /\ round_up8 (16 + v) mod 8 = 0.
Proof.
  intros v Hv. rewrite round_up8_eq by lia. pose proof (pad8_bound (16 + v)). pose proof (pad8_eq (16 + v)) as E.
  split; [lia|]. rewrite E, Z.mul_comm. apply Z.mod_mul. lia.
Qed.

(** The model's tests at a 4-aligned offset. *)
Lemma ua_obj : is_object_type bs POD_OBJECT_PROPS =
  (u32_at bs 0 <? 1048576) && (u32_at bs 4 =? 15) && (8 <=? u32_at bs 0) && (u32_at bs 8 =? 262146).
Proof. reflexivity. Qed.

Lemma ua_pin : forall size r, r mod 4 = 0 -> 8 <= r ->
  prop_is_inside bs 8 size r = (16 <=? size) && (r - 8 <=? size - 16) && (u32_at bs (r + 8) <=? 8 + size - (r + 16)).
Proof.
  intros size r H4 H8. unfold prop_is_inside, ptr_type_inside, ptrinside, ptr_remaining.
  rewrite (proj2 (Z.eqb_eq _ _) H4), (proj2 (Z.leb_le _ _) H8). reflexivity.
Qed.

Lemma ua_fp_in : forall size key r n, prop_is_inside bs 8 size r = true ->
  find_prop bs size key r (S n) =
  if u32_at bs r =? key then Some r else find_prop bs size key (r + round_up8 (16 + u32_at bs (r + 8))) n.
Proof. intros size key r n H. rewrite find_prop_step, H. reflexivity. Qed.

Lemma ua_fp_out : forall size key r n, prop_is_inside bs 8 size r = false -> find_prop bs size key r (S n) = None.
Proof. intros size key r n H. rewrite find_prop_step, H. reflexivity. Qed.

Lemma ua_is_struct : forall v, is_struct_at bs v = (u32_at bs v <? 1048576) && (u32_at bs (v + 4) =? 14).
Proof. reflexivity. Qed.

(** A Struct of fewer than 8 bytes has no child. *)
Lemma ua_walk_small : forall body vs c n, vs < 8 -> walk_res bs body vs c (S n) None = (None, 0).
Proof.
  intros body vs c n H. rewrite walk_res_step.
  replace (pod_is_inside bs body vs c) with false; [reflexivity|].
  symmetry. unfold pod_is_inside, ptr_type_inside, ptrinside.
  rewrite (proj2 (Z.leb_gt 8 vs) H). destruct (c mod 4 =? 0), (body <=? c); reflexivity.
Qed.

(** Branch tests: the condition of the pc's [if], decided on Z. *)
Ltac ua_lia := first [ lia | Z.div_mod_to_equations; lia ].
Ltac ua_cond_base :=
  first [ reflexivity
        | apply Z.ltb_lt; ua_lia | apply Z.ltb_ge; ua_lia
        | apply Z.leb_le; ua_lia | apply Z.leb_gt; ua_lia
        | apply Z.eqb_eq; ua_lia | apply Z.eqb_neq; ua_lia ].
Ltac ua_cond_rec :=
  lazymatch goal with
  | |- negb _ = true => apply (proj2 (Bool.negb_true_iff _)); ua_cond_rec
  | |- negb _ = false => apply (proj2 (Bool.negb_false_iff _)); ua_cond_rec
  | _ => ua_cond_base
  end.
Ltac ua_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb]; zsimp; rewrite ?ua_land3; ua_cond_rec.
Ltac ua_go b :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => replace c with b; [cbv iota | symmetry; ua_cond]
  end.
Ltac ua_eq := first [ reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ].

(** ** The epilogue from 0x148f0: a0 = a1, the nine reloads, sp back, ret; a1 holds the answer. (0x148ec is
    `li a1,-1` then 0x148f0.) *)
Lemma epi : forall m j (F' : bvmap 5 word) (fc' : bv 32) rc
    (x1 y0 y1 y2 x8 x9 w10 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  rc = snd RES ->
  (forall k : bv 5, ~ (13 <= bv_unsigned k <= 15) -> Sem.reg_get F' k = Sem.reg_get F k) -> frm0 fc' ->
  rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  stk rsegs m lo (bv_unsigned sp + -80) -> mem_inv rsegs m -> wmono rsegs mi m ->
  role_mem mi m (bv_unsigned sp) Q (fst RES) ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 (Z_to_bv 64 rc)
                       w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F' (Z_to_bv 64 0x148f0) fc' None m (seg_rom rsegs)).
Proof.
  intros m j F' fc' rc x1 y0 y1 y2 x8 x9 w10 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    Erc HF' HFC FR ST MI WM RM.
  pose proof args_facts as (_ & _ & _ & _ & _ & _ & _ & LO0 & _ & HL).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  do 11 zstep. (* mv a0,a1; nine ld; addi sp *)
  release_frame FR ST (bv_unsigned sp).
  zstep. (* ret *)
  subst rc.
  finish.
Qed.

(** *** The value read: the child's words, the model's answer, the register forms *)
Lemma uc_u32_range : forall o, 0 <= u32_at bs o < 2^32.
Proof. intros o. unfold u32_at. apply rd32_range. Qed.

Lemma uc_body : forall o, 4 <= u32_at bs o -> rd32 (e_body (child_at bs o)) = u32_at bs (o + 8).
Proof.
  intros o H. unfold child_at. cbn [e_body]. unfold rd32 at 1. rewrite firstn_firstn.
  replace (Nat.min 4 (Z.to_nat (u32_at bs o))) with 4%nat by lia. reflexivity.
Qed.

Lemma uc_res_big : forall o, 2^20 <= u32_at bs o -> spa_role_value (child_at bs o) = (None, -1).
Proof.
  intros o H. unfold spa_role_value, spa_get_int, spa_get_float.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  unfold SPA_POD_MAX_SIZE. rewrite (proj2 (Z.ltb_ge _ _) H). reflexivity.
Qed.

Lemma uc_res_int : forall o, u32_at bs o < 2^20 -> 4 <= u32_at bs o -> u32_at bs (o + 4) = 4 ->
  spa_role_value (child_at bs o) = flag_rc (s32 (u32_at bs (o + 8))).
Proof.
  intros o H1 H2 H3. unfold spa_role_value, spa_get_int.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  replace (e_type (child_at bs o)) with (u32_at bs (o + 4)) by reflexivity.
  unfold SPA_POD_MAX_SIZE, POD_INT. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
  rewrite (uc_body o H2). reflexivity.
Qed.

Lemma uc_res_bad : forall o, u32_at bs o < 2^20 ->
  (u32_at bs o < 4 \/ (u32_at bs (o + 4) <> 4 /\ u32_at bs (o + 4) <> 6)) ->
  spa_role_value (child_at bs o) = (None, -1).
Proof.
  intros o H1 H2. unfold spa_role_value, spa_get_int, spa_get_float.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  replace (e_type (child_at bs o)) with (u32_at bs (o + 4)) by reflexivity.
  unfold SPA_POD_MAX_SIZE, POD_INT, POD_FLOAT. rewrite (proj2 (Z.ltb_lt _ _) H1).
  destruct H2 as [H2|[H3 H4]].
  - rewrite (proj2 (Z.leb_gt _ _) H2). rewrite !andb_false_r. reflexivity.
  - rewrite (proj2 (Z.eqb_neq _ _) H3), (proj2 (Z.eqb_neq _ _) H4). reflexivity.
Qed.

Lemma uc_res_flt : forall o, u32_at bs o < 2^20 -> 4 <= u32_at bs o -> u32_at bs (o + 4) = 6 ->
  spa_role_value (child_at bs o) =
  match nearest (u32_at bs (o + 8)) INT32_MIN INT32_MAX with Some n => flag_rc n | None => (None, -1) end.
Proof.
  intros o H1 H2 H3. unfold spa_role_value, spa_get_int, spa_get_float.
  replace (e_size (child_at bs o)) with (u32_at bs o) by reflexivity.
  replace (e_type (child_at bs o)) with (u32_at bs (o + 4)) by reflexivity.
  unfold SPA_POD_MAX_SIZE, POD_INT, POD_FLOAT. rewrite H3, (proj2 (Z.ltb_lt _ _) H1), (proj2 (Z.leb_le _ _) H2).
  rewrite (uc_body o H2). reflexivity.
Qed.

Lemma uc_near_rng : forall b lo' hi' n, nearest b lo' hi' = Some n -> lo' <= n <= hi'.
Proof.
  intros b lo' hi' n. unfold nearest. destruct (near_f32 b) as [r|]; [|discriminate].
  destruct ((lo' <=? r) && (r <=? hi')) eqn:E; [|discriminate]. intros Hn. injection Hn as <-.
  apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
Qed.

(** The pod bytes, read in any frame memory. *)
Lemma uc_rd : forall m o n, frame m -> 0 <= o -> o + Z.of_nat n <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (P + o)) n = Some (firstn n (skipn (Z.to_nat o) bs)).
Proof. intros m o n FR Ho Hn. apply (bytes_at_read rsegs m P bs o n (pod_at m FR)); lia. Qed.

Lemma uc_rd1 : forall m o b, frame m -> 0 <= o -> nth_error bs (Z.to_nat o) = Some b ->
  ov_read_bytes rsegs m (wa (P + o)) 1 = Some [b].
Proof.
  intros m o b FR Ho E.
  assert (L : (Z.to_nat o < length bs)%nat) by (apply nth_error_Some; congruence).
  rewrite (uc_rd m o 1 FR Ho) by lia.
  rewrite <- (firstn_skipn_step bs (Z.to_nat o) 0 b E). reflexivity.
Qed.

Lemma uc_bytes4 : forall o, 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  exists b8 b9 b10 b11, nth_error bs (Z.to_nat o) = Some b8 /\ nth_error bs (Z.to_nat (o + 1)) = Some b9 /\
    nth_error bs (Z.to_nat (o + 2)) = Some b10 /\ nth_error bs (Z.to_nat (o + 3)) = Some b11 /\
    u32_at bs o = bytes_le_to_Z [b8; b9; b10; b11].
Proof.
  intros o H0 H4.
  exists (nth (Z.to_nat o) bs NUL), (nth (Z.to_nat (o + 1)) bs NUL), (nth (Z.to_nat (o + 2)) bs NUL),
    (nth (Z.to_nat (o + 3)) bs NUL).
  split; [apply nth_error_nth'; lia|]. split; [apply nth_error_nth'; lia|].
  split; [apply nth_error_nth'; lia|]. split; [apply nth_error_nth'; lia|].
  unfold u32_at, rd32.
  rewrite <- (firstn_skipn_step bs (Z.to_nat o) 3 (nth (Z.to_nat o) bs NUL)) by (apply nth_error_nth'; lia).
  rewrite <- (firstn_skipn_step bs (S (Z.to_nat o)) 2 (nth (Z.to_nat (o + 1)) bs NUL))
    by (replace (S (Z.to_nat o)) with (Z.to_nat (o + 1)) by lia; apply nth_error_nth'; lia).
  rewrite <- (firstn_skipn_step bs (S (S (Z.to_nat o))) 1 (nth (Z.to_nat (o + 2)) bs NUL))
    by (replace (S (S (Z.to_nat o))) with (Z.to_nat (o + 2)) by lia; apply nth_error_nth'; lia).
  rewrite <- (firstn_skipn_step bs (S (S (S (Z.to_nat o)))) 0 (nth (Z.to_nat (o + 3)) bs NUL))
    by (replace (S (S (S (Z.to_nat o)))) with (Z.to_nat (o + 3)) by lia; apply nth_error_nth'; lia).
  reflexivity.
Qed.

(** lw of the 4 bytes l: the sign-extended u32. *)
Lemma uc_swrap32 : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Lemma uc_lw : forall l, sext 64 (bv_extract 0 32 (le_bytes_to_word (firstn 4 l))) = Z_to_bv 64 (s32 (rd32 l)).
Proof.
  intros l. pose proof (rd32_range l) as R. unfold rd32 in *.
  rewrite sext_small. f_equal. rewrite signed_of_extract by lia.
  unfold le_bytes_to_word. rewrite unsigned_lit by lia. rewrite uc_swrap32. unfold s32.
  destruct (Z.ltb_spec (bytes_le_to_Z (firstn 4 l)) (2^31)); Z.div_mod_to_equations; lia.
Qed.

(** flw of the 4 bytes of a u32 b stored by sw. *)
Lemma uc_flw : forall b, 0 <= b < 2^32 -> bv_extract 0 32 (le_bytes_to_word (le4 (Z_to_bv 64 b))) = Z_to_bv 32 b.
Proof.
  intros b Hb. apply bv_eq. rewrite extract_low_mod by lia. rewrite le_bytes_to_word_le4.
  rewrite unsigned_lit by lia. rewrite Z_to_bv_unsigned. change (Z.of_N 32) with 32.
  change (bv_wrap 32 b) with (b mod 2^32). rewrite !Z.mod_small by lia. reflexivity.
Qed.

(** The four lbu, slli and or of the Float body (body.h:202): the u32 of the 4 bytes. *)
Lemma uc_lor_shl : forall x y k, 0 <= k -> 0 <= x -> 0 <= y < 2^k -> Z.lor (Z.shiftl x k) y = x * 2^k + y.
Proof.
  intros x y k Hk Hx Hy. rewrite Z.shiftl_mul_pow2 by lia.
  assert (L : Z.land (x * 2^k) y = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i k) as [Hik|Hik].
    - rewrite Z.mul_pow2_bits_low by lia. reflexivity.
    - rewrite <- (Z.mod_small y (2^k)) by lia. rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
  rewrite <- (Z.lxor_lor _ _ L), <- (Z.add_nocarry_lxor _ _ L). reflexivity.
Qed.

Lemma uc_asm : forall b8 b9 b10 b11 : byte,
  Z.lor (Z.lor (Z.shiftl (bv_unsigned b11) 24) (Z.shiftl (bv_unsigned b10) 16))
        (Z.lor (Z.shiftl (bv_unsigned b9) 8) (bv_unsigned b8)) = bytes_le_to_Z [b8; b9; b10; b11].
Proof.
  intros b8 b9 b10 b11.
  pose proof (byte_range b8) as R8. pose proof (byte_range b9) as R9.
  pose proof (byte_range b10) as R10. pose proof (byte_range b11) as R11.
  assert (E1 : Z.lor (Z.shiftl (bv_unsigned b9) 8) (bv_unsigned b8) = bv_unsigned b9 * 2^8 + bv_unsigned b8)
    by (apply uc_lor_shl; lia).
  assert (E2 : Z.lor (Z.shiftl (bv_unsigned b11) 24) (Z.shiftl (bv_unsigned b10) 16) =
               Z.shiftl (bv_unsigned b11 * 2^8 + bv_unsigned b10) 16).
  { rewrite (Z.shiftl_mul_pow2 (bv_unsigned b10) 16) by lia.
    rewrite (Z.shiftl_mul_pow2 (bv_unsigned b11 * 2^8 + bv_unsigned b10) 16) by lia.
    rewrite uc_lor_shl by lia. lia. }
  rewrite E1, E2. rewrite uc_lor_shl by lia.
  cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
  rewrite (lor_low_shiftl (bv_unsigned b10) (bv_unsigned b11)) by lia.
  rewrite (lor_low_shiftl (bv_unsigned b9) (bv_unsigned b10 + bv_unsigned b11 * 256)) by lia.
  rewrite (lor_low_shiftl (bv_unsigned b8) (bv_unsigned b9 + (bv_unsigned b10 + bv_unsigned b11 * 256) * 256)) by lia.
  lia.
Qed.

Lemma uc_shl_rng : forall (b : byte) k, 0 <= k <= 24 -> 0 <= Z.shiftl (bv_unsigned b) k < 2^32.
Proof.
  intros b k Hk. pose proof (byte_range b) as R. rewrite Z.shiftl_mul_pow2 by lia.
  assert (2^k <= 2^24) by (apply Z.pow_le_mono_r; lia). assert (0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
  nia.
Qed.

Lemma uc_ub : forall b : byte, bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b.
Proof. intros b. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

Lemma uc_us : forall (b : byte) k, 0 <= k <= 24 ->
  bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned b) k)) = Z.shiftl (bv_unsigned b) k.
Proof. intros b k Hk. apply unsigned_lit. pose proof (uc_shl_rng b k Hk). lia. Qed.

Lemma uc_ul : forall x y, 0 <= x < 2^32 -> 0 <= y < 2^32 -> bv_unsigned (Z_to_bv 64 (Z.lor x y)) = Z.lor x y.
Proof. intros x y Hx Hy. apply unsigned_lit. pose proof (Z_lor_lt_pow2 x y 32 Hx Hy). lia. Qed.

Ltac uc_rng32 :=
  lazymatch goal with
  | |- 0 <= Z.lor _ _ < 2^32 => apply Z_lor_lt_pow2; uc_rng32
  | |- 0 <= Z.shiftl (bv_unsigned _) _ < 2^32 => apply uc_shl_rng; lia
  | |- 0 <= bv_unsigned ?b < 2^32 => pose proof (byte_range b); lia
  end.

Lemma uc_asm_word : forall b8 b9 b10 b11 : byte,
  v_or (v_or (v_slli (zxb b11) 24) (v_slli (zxb b10) 16)) (v_or (v_slli (zxb b9) 8) (zxb b8)) =
  Z_to_bv 64 (bytes_le_to_Z [b8; b9; b10; b11]).
Proof.
  intros b8 b9 b10 b11. rewrite <- uc_asm. unfold v_or, v_slli, zxb. f_equal.
  rewrite !uc_ub. rewrite !uc_us by lia. rewrite !uc_ul by uc_rng32. reflexivity.
Qed.

(** The branch tests of the value read. *)
Lemma uc_c_shr : forall u, 0 <= u < 2^32 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 u)) 20)) (Z_to_bv 64 0) = (u <? 2^20).
Proof.
  intros u Hu. unfold bv_eqb. rewrite (unsigned_lit u) by lia. rewrite Z.shiftr_div_pow2 by lia.
  assert (D : 0 <= u / 2^20 < 2^12) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (unsigned_lit (u / 2^20)) by lia. rewrite (unsigned_lit 0) by lia.
  destruct (Z.ltb_spec u (2^20)).
  - apply Z.eqb_eq. apply Z.div_small. lia.
  - apply Z.eqb_neq. assert (0 < u / 2^20) by (apply Z.div_str_pos; lia). lia.
Qed.

Lemma uc_c_ltu : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y).
Proof. intros x y Hx Hy. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma uc_c_eq_s32 : forall t k, 0 <= t < 2^32 -> 0 <= k < 2^31 ->
  bv_eqb (Z_to_bv 64 (s32 t)) (Z_to_bv 64 k) = (t =? k).
Proof.
  intros t k Ht Hk. unfold bv_eqb, s32. rewrite (unsigned_lit k) by lia.
  destruct (Z.ltb_spec t (2^31)).
  - rewrite unsigned_lit by lia. reflexivity.
  - rewrite unsigned_lit_wrap. rewrite (proj2 (Z.eqb_neq t k)) by lia. apply Z.eqb_neq.
    Z.div_mod_to_equations. lia.
Qed.

(** The switch's compares (0x1481c, 0x14824) on a 32-bit value, the role cell's null test (0x14828). *)
Lemma uc_eq_s : forall v k, -2^31 <= v < 2^31 -> -2^31 <= k < 2^31 ->
  bv_eqb (Z_to_bv 64 v) (Z_to_bv 64 k) = (v =? k).
Proof.
  intros v k Hv Hk. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec v k) as [->|N]; [apply Z.eqb_refl|].
  apply Z.eqb_neq. intros E. apply N. Z.div_mod_to_equations. lia.
Qed.

Lemma uc_eqb_lit : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

(** sext.w (0x14814) of a 32-bit value. *)
Lemma uc_sextw : forall v, -2^31 <= v < 2^31 ->
  Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 v) + 0)) = Z_to_bv 64 v.
Proof.
  intros v Hv. f_equal. rewrite Z.add_0_r, unsigned_lit_wrap, uc_swrap32. Z.div_mod_to_equations. lia.
Qed.

(** t and t - 1 as 64-bit words, from their signed values (reac_float_near.h:30-31). *)
Lemma uc_bv_mod : forall x y, x mod 2^64 = y mod 2^64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned.
  change (bv_wrap 64 x) with (x mod 2^64). change (bv_wrap 64 y) with (y mod 2^64). exact H.
Qed.

Lemma uc_signed : forall t : word, bv_signed t mod 2^64 = bv_unsigned t.
Proof.
  intros t. pose proof (bv_unsigned_in_range 64 t) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2^64) in R.
  rewrite zb_signed. destruct (Z.ltb_spec (bv_unsigned t) (2^63)).
  - apply Z.mod_small. lia.
  - replace (bv_unsigned t - 2^64) with (bv_unsigned t + (-1) * 2^64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.

Lemma uc_t0 : forall t : word, t = Z_to_bv 64 (bv_signed t - 0).
Proof.
  intros t. rewrite Z.sub_0_r. symmetry. transitivity (Z_to_bv 64 (bv_unsigned t)); [|apply Z_to_bv_lit_self].
  apply uc_bv_mod. rewrite uc_signed. pose proof (bv_unsigned_in_range 64 t) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 64) with (2^64) in R. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma uc_dec : forall (t : word) e, e = bv_unsigned t + -1 -> Z_to_bv 64 e = Z_to_bv 64 (bv_signed t - 1).
Proof.
  intros t e ->. apply uc_bv_mod. rewrite <- (uc_signed t). rewrite Zplus_mod_idemp_l. f_equal; lia.
Qed.

(** The `r--` check (0x148e0 `bge a1,a0` with a1 = t - 1): not taken when t >= -2^31. *)
Lemma uc_lts : forall t : word, -2^31 <= bv_signed t -> bv_lts (Z_to_bv 64 (bv_unsigned t + -1)) t = true.
Proof.
  intros t Ht. unfold bv_lts. apply Z.ltb_lt.
  pose proof (bv_unsigned_in_range 64 t) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  rewrite (zb_signed t) in Ht |- *. rewrite zb_signed. rewrite unsigned_lit_wrap.
  destruct (Z.ltb_spec (bv_unsigned t) (2^63)); destruct (Z.ltb_spec ((bv_unsigned t + -1) mod 2^64) (2^63));
    Z.div_mod_to_equations; lia.
Qed.

(** reac_float_nearest's double steps (Prog/ParseFP.v) with INT32_MIN, INT32_MAX and the five constants: the
    answer, and on the range test's pass the two cast bounds and t >= -2^31. *)
Lemma uc_hw : forall b, 0 <= b < 2^32 ->
  (nearest b INT32_MIN INT32_MAX =
     if rfn_in b (Z_to_bv 64 0xc1e0000000000000) (Z_to_bv 64 0x41e0000000000000) then Some (rfn_r b) else None) /\
  (rfn_in b (Z_to_bv 64 0xc1e0000000000000) (Z_to_bv 64 0x41e0000000000000) = true ->
     flt_d (Z_to_bv 64 0xc3e0000000000001) (rfn_d b) = true /\
     flt_d (rfn_d b) (Z_to_bv 64 0x43e0000000000000) = true /\
     -2^31 <= bv_signed (rfn_t b)).
Proof.
  intros b Hb. pose proof role_consts as (CL & CH & C3 & C4).
  assert (CH' : f64_is_int (Z_to_bv 64 0x41e0000000000000) (INT32_MAX + 1) = true)
    by (replace (INT32_MAX + 1) with (2^31) by (unfold INT32_MAX; lia); exact CH).
  assert (L1 : -2^53 <= INT32_MIN) by (unfold INT32_MIN; lia).
  assert (L2 : INT32_MAX < 2^53) by (unfold INT32_MAX; lia).
  split; [apply rfn_hw_nearest; [exact Hb | exact L1 | exact L2 | exact CL | exact CH']|].
  intros HIN. split; [|split].
  - apply (rfn_hw_above b INT32_MIN INT32_MAX _ _ Hb L1 L2 CL CH' HIN _ (-2^63 - 2^11) C3).
    unfold INT32_MIN. lia.
  - apply (rfn_hw_below b INT32_MIN INT32_MAX _ _ Hb L1 L2 CL CH' HIN _ (2^63) C4).
    unfold INT32_MAX. lia.
  - pose proof (rfn_hw_t_range b INT32_MIN INT32_MAX _ _ Hb L1 L2 CL CH' HIN) as T.
    unfold INT32_MIN in T. lia.
Qed.

(** The FP registers other than f13-f15 are F's. *)
Ltac uc_fregs :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  repeat (rewrite freg_get_other;
          [|unfold bv_eqb; apply Z.eqb_neq;
            lazymatch goal with |- bv_unsigned ?r <> _ =>
              let v := eval vm_compute in (bv_unsigned r) in change (bv_unsigned r) with v end;
            lia]);
  reflexivity.

(** A store of 4 bytes to the role cell. *)
Lemma uc_cell_st : forall m cs (v : word),
  rw_cells rsegs m (bv_unsigned sp + -80) cs -> Z.of_nat (cells_size cs) = 80 ->
  stk rsegs m lo (bv_unsigned sp + -80) -> munch [(bv_unsigned sp - PARSE_FRAME, bv_unsigned sp)] mi m ->
  wmono rsegs mi m -> mem_inv rsegs m -> wr_at rsegs m Q 4 ->
  rw_cells rsegs (write_to_mem m (Z_to_bv 64 Q) (le4 v)) (bv_unsigned sp + -80) cs /\
  stk rsegs (write_to_mem m (Z_to_bv 64 Q) (le4 v)) lo (bv_unsigned sp + -80) /\
  munch [(bv_unsigned sp - PARSE_FRAME, bv_unsigned sp); (Q, Q + 4)] mi (write_to_mem m (Z_to_bv 64 Q) (le4 v)) /\
  wmono rsegs mi (write_to_mem m (Z_to_bv 64 Q) (le4 v)) /\ mem_inv rsegs (write_to_mem m (Z_to_bv 64 Q) (le4 v)) /\
  bytes_at rsegs (write_to_mem m (Z_to_bv 64 Q) (le4 v)) Q (le4 v).
Proof.
  intros m cs v FR HC ST MU WM MI WQ.
  pose proof args_facts as (_ & _ & _ & _ & _ & _ & HSQ & _ & _ & _).
  pose proof WQ as (HQ0 & HQ4 & _).
  change (Z_to_bv 64 Q) with (wa Q).
  split; [apply rw_cells_frame; [exact FR | lia | rewrite length_le4; lia | left; rewrite HC; lia]|].
  split; [apply stk_write; [exact ST | lia | rewrite length_le4; lia]|].
  split.
  { apply munch_write; [| lia | rewrite length_le4; lia | rewrite length_le4; cbn [inside]; right; left; lia].
    apply (munch_weaken [(bv_unsigned sp - PARSE_FRAME, bv_unsigned sp)]); [|exact MU].
    intros x [Hx _]. split; [exact Hx | exact I]. }
  split; [apply wmono_write; exact WM|].
  split.
  { apply mem_inv_store; [exact MI|]. rewrite length_le4.
    replace (wa Q) with (wa (Q + 0)) by (f_equal; lia). apply (wr_at_store_ok rsegs m Q 4 0 4 WQ); lia. }
  apply bytes_at_write_same; [lia | rewrite length_le4; lia].
Qed.

(** From 0x148ec: a1 = -1, then the epilogue. *)
Lemma uc_neg1 : forall m (F' : bvmap 5 word) (fc' : bv 32)
    (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  RES = (None, -1) ->
  (forall k : bv 5, ~ (13 <= bv_unsigned k <= 15) -> Sem.reg_get F' k = Sem.reg_get F k) -> frm0 fc' ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F' (Z_to_bv 64 0x148ec) fc' None m (seg_rom rsegs)).
Proof.
  intros m F' fc' x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    HR HF HC ((j & FR) & ST & MU & WM & MI).
  step.
  eapply epi; [| exact HF | exact HC | exact FR | exact ST | exact MI | exact WM |].
  - rewrite HR. reflexivity.
  - rewrite HR. exact MU.
Qed.

(** From 0x14828 with a0 = v, 0 or 1: the role cell's null and alignment checks (not taken: Q >= sp > 0,
    Q mod 4 = 0), the store and the return of 1. *)
Lemma uc_st : forall m (F' : bvmap 5 word) (fc' : bv 32) v
    (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  x8 = Z_to_bv 64 Q -> w10 = Z_to_bv 64 v -> v = 0 \/ v = 1 -> flag_rc v = RES ->
  (forall k : bv 5, ~ (13 <= bv_unsigned k <= 15) -> Sem.reg_get F' k = Sem.reg_get F k) -> frm0 fc' ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F' (Z_to_bv 64 0x14828) fc' None m (seg_rom rsegs)).
Proof.
  intros m F' fc' v x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    E8 E10 H01 HRv HF HC FRM.
  subst x8 w10.
  pose proof args_facts as (L8 & HS0 & HP0 & HP16 & HPL & HQ4 & HSQ & HLO0 & HSP & HLSP).
  pose proof (cell_wr m FRM) as WQ. pose proof WQ as (HQ0 & HQL & _).
  destruct FRM as ((j & FR) & ST & MU & WM & MI).
  pose proof (wr_at_store_ok rsegs m Q 4 0 4 WQ ltac:(lia) ltac:(lia)) as HS. rewrite Z.add_0_r in HS.
  assert (L3 : Z.land Q 3 = 0) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; exact HQ4).
  step. rewrite (uc_eqb_lit Q 0) by lia. if_false.
  step. step. rewrite (unsigned_lit Q) by lia. rewrite L3. if_false.
  step.
  destruct (uc_cell_st m _ (Z_to_bv 64 v) FR eq_refl ST MU WM MI WQ) as (FR' & ST' & MU' & WM' & MI' & BQ).
  clear HS. set (m' := write_to_mem m (Z_to_bv 64 Q) (le4 (Z_to_bv 64 v))) in *. clearbody m'.
  step. step.
  eapply epi; [| exact HF | exact HC | exact FR' | exact ST' | exact MI' | exact WM' |].
  - destruct H01 as [->| ->]; rewrite <- HRv; reflexivity.
  - destruct H01 as [->| ->]; rewrite <- HRv; exact (conj MU' BQ).
Qed.

(** From 0x14814 with a0 = v (body.h:172, or the Float's nearest): sext.w and the switch (reac_role_cfg.c:97-100),
    then the store or -1. *)
Lemma uc_sw : forall m (F' : bvmap 5 word) (fc' : bv 32) v
    (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  x8 = Z_to_bv 64 Q -> w10 = Z_to_bv 64 v -> -2^31 <= v < 2^31 -> flag_rc v = RES ->
  (forall k : bv 5, ~ (13 <= bv_unsigned k <= 15) -> Sem.reg_get F' k = Sem.reg_get F k) -> frm0 fc' ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F' (Z_to_bv 64 0x14814) fc' None m (seg_rom rsegs)).
Proof.
  intros m F' fc' v x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    E8 E10 Hv HRv HF HC FRM.
  subst x8 w10.
  step. rewrite (uc_sextw v Hv).
  step. step. rewrite (uc_eq_s v 1) by lia.
  destruct (Z.eqb_spec v 1) as [->|N1].
  { (* the beq's [if] reduced with the test *)
    eapply uc_st; [reflexivity | reflexivity | right; reflexivity | exact HRv | exact HF | exact HC | exact FRM]. }
  step. step. rewrite (uc_eq_s v 0) by lia.
  destruct (Z.eqb_spec v 0) as [->|N0].
  { if_false. eapply uc_st; [reflexivity | reflexivity | left; reflexivity | exact HRv | exact HF | exact HC | exact FRM]. }
  if_true.
  destruct FRM as ((j & FR) & ST & MU & WM & MI).
  assert (HR : RES = (None, -1)).
  { rewrite <- HRv. unfold flag_rc. rewrite (proj2 (Z.eqb_neq v 0) N0), (proj2 (Z.eqb_neq v 1) N1). reflexivity. }
  eapply epi; [| exact HF | exact HC | exact FR | exact ST | exact MI | exact WM |].
  - rewrite HR. reflexivity.
  - rewrite HR. exact MU.
Qed.

(** From 0x14878 with a0 = b, the Float body's u32: the store to the float temp, flw, and reac_float_nearest
    (reac_float_near.h:24-34) with ParseFP's double steps, the two cast bounds and the `r--` check, then 0x14814
    or -1. *)
Lemma uc_flt : forall b m
    (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  0 <= b < 2^32 -> x8 = Z_to_bv 64 Q -> w10 = Z_to_bv 64 b -> w11 = Z_to_bv 64 0x10870 ->
  RES = match nearest b INT32_MIN INT32_MAX with Some n => flag_rc n | None => (None, -1) end ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x14878) fc None m (seg_rom rsegs)).
Proof.
  intros b m x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    Hb E8 E10 E11 HRES FRM.
  subst x8 w10 w11.
  (* the FP steps drop every other [frm0] hypothesis: keep the section's one under a wrapper *)
  pose proof HFRM as HFRM0. change (id (frm0 fc)) in HFRM0.
  destruct (uc_hw b Hb) as [HN HW].
  unfold rfn_in in HN.
  pose proof args_facts as (L8 & HS0 & HP0 & HP16 & HPL & HQ4 & HSQ & HLO0 & HSP & HLSP).
  pose proof (cell_wr m FRM) as WQ.
  destruct FRM as ((j & FR) & ST & MU & WM & MI).
  unfold PARSE_FRAME in MU.
  step. step.
  rewrite (uc_flw b Hb).
  lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?c2 :: ?rest) =>
    apply (rw_cells_merge rsegs _ _ [] [c1; c2] rest) in FR end.
  cbn [app cells_size csize Nat.add] in FR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (FRF : frame mm)
      by (unfold frame, PARSE_FRAME; split; [eexists; exact FR | split; [exact ST | split; [exact MU | split; [exact WM | exact MI]]]])
  end.
  clear FR ST MU WM WQ.
  step. step. step. step. step.
  change (fadd_d RNE (fcvt_d_s RNE (Sem.nan_box (Z_to_bv 32 b))) (Z_to_bv 64 0x3FE0000000000000)) with (rfn_d b).
  step. step.
  destruct (fle_d (Z_to_bv 64 0xc1e0000000000000) (rfn_d b)) eqn:E1; try rewrite E1 in HN.
  2: { change (bword false) with (Z_to_bv 64 0). if_true. pose proof (HFRM0 : frm0 fc) as HFRM.
       eapply uc_neg1; [rewrite HRES, HN; reflexivity | uc_fregs | assumption | exact FRF]. }
  change (bword true) with (Z_to_bv 64 1). if_false.
  step. step. step. step.
  destruct (flt_d (rfn_d b) (Z_to_bv 64 0x41e0000000000000)) eqn:E2; try rewrite E2 in HN.
  2: { change (bword false) with (Z_to_bv 64 0). if_true. pose proof (HFRM0 : frm0 fc) as HFRM.
       eapply uc_neg1; [rewrite HRES, HN; reflexivity | uc_fregs | assumption | exact FRF]. }
  change (bword true) with (Z_to_bv 64 1). if_false.
  cbn [andb] in HN.
  destruct (HW ltac:(unfold rfn_in; rewrite E1, E2; reflexivity)) as (HA & HB & HT). clear HW.
  pose proof (uc_near_rng _ _ _ _ HN) as R. unfold INT32_MIN, INT32_MAX in R.
  assert (HF : flag_rc (rfn_r b) = RES) by (rewrite HRES, HN; reflexivity).
  clear HRES.
  (* the cast bounds (0x148b8, 0x148c8): -2^63 - 2^11 < d < 2^63 *)
  step. step. step. step.
  rewrite HA. change (bword true) with (Z_to_bv 64 1). if_false.
  step. step. step. step.
  rewrite HB. change (bword true) with (Z_to_bv 64 1). if_false.
  step.
  change (fcvt_l_d RTZ (rfn_d b)) with (rfn_t b).
  step. step.
  destruct (flt_d (rfn_d b) (fcvt_d_l RNE (rfn_t b))) eqn:E3.
  - change (bword true) with (Z_to_bv 64 1). step. if_false.
    step. step. rewrite (uc_lts (rfn_t b) HT). if_false.
    step. step. pose proof (HFRM0 : frm0 fc) as HFRM.
    eapply (uc_sw _ _ _ (rfn_r b)); [reflexivity | | lia | exact HF | uc_fregs | assumption | exact FRF].
    unfold rfn_r. rewrite E3. apply uc_dec. lia.
  - change (bword false) with (Z_to_bv 64 0). step. if_true. pose proof (HFRM0 : frm0 fc) as HFRM.
    eapply (uc_sw _ _ _ (rfn_r b)); [reflexivity | | lia | exact HF | uc_fregs | assumption | exact FRF].
    unfold rfn_r. rewrite E3. apply uc_t0.
Qed.

(** ** The value read from 0x147f8: the child at offset c of the pod is the key's value (spa_pod_get_int, else
    spa_pod_get_float and reac_float_nearest with its cast and `r--` checks; then the switch, the null and alignment
    checks of the role cell, the store and the return). s7 holds its size. *)
Lemma value_tail : null = false -> forall c m
    (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  x8 = Z_to_bv 64 Q -> x18 = Z_to_bv 64 (P + c) -> x23 = Z_to_bv 64 (u32_at bs c) ->
  16 <= c -> c mod 8 = 0 -> c + 8 + u32_at bs c <= Z.of_nat (length bs) ->
  spa_role_value (child_at bs c) = RES ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x147f8) fc None m (seg_rom rsegs)).
Proof.
  intros HNULL c m x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    E8 E18 E23 Hc16 Hc8 Hcl HV FRM.
  subst x8 x18 x23.
  pose proof args_facts as (L8 & HS0 & HP0 & HP16 & HPL & HQ4 & HSQ & HLO0 & HSP & HLSP).
  pose proof (uc_u32_range c) as Hu. pose proof (uc_u32_range (c + 4)) as Ht.
  pose proof (uc_u32_range (c + 8)) as Hb.
  step. step.
  rewrite (uc_c_shr _ Hu).
  destruct (Z.ltb_spec (u32_at bs c) (2^20)) as [Hu20|Hu20].
  2: { if_true. eapply uc_neg1; [| intros k Hk; reflexivity | exact HFRM | exact FRM].
       rewrite <- HV. apply uc_res_big. exact Hu20. }
  if_false.
  pose proof (uc_rd m (c + 4) 4 FRM ltac:(lia) ltac:(lia)) as HR.
  step. clear HR.
  rewrite (uc_lw (skipn (Z.to_nat (c + 4)) bs)).
  change (rd32 (skipn (Z.to_nat (c + 4)) bs)) with (u32_at bs (c + 4)).
  step. step.
  rewrite (uc_c_ltu (u32_at bs c) 4) by lia.
  destruct (Z.ltb_spec (u32_at bs c) 4) as [Hu4|Hu4].
  { (* the bltu's [if] reduced with the test *)
    step. rewrite (uc_c_ltu (u32_at bs c) 4) by lia. if_true.
    eapply uc_neg1; [| intros k Hk; reflexivity | exact HFRM | exact FRM].
    rewrite <- HV. apply uc_res_bad; [exact Hu20 | left; exact Hu4]. }
  step.
  rewrite (uc_c_eq_s32 (u32_at bs (c + 4)) 4) by lia.
  destruct (Z.eqb_spec (u32_at bs (c + 4)) 4) as [Ht4|Ht4].
  { (* Int (body.h:165-173) *)
    if_false.
    pose proof (uc_rd m (c + 8) 4 FRM ltac:(lia) ltac:(lia)) as HR.
    step. clear HR.
    eapply (uc_sw _ _ _ (s32 (u32_at bs (c + 8)))); [reflexivity | apply uc_lw | apply s32_range; exact Hb
      | | intros k Hk; reflexivity | exact HFRM | exact FRM].
    rewrite <- HV. symmetry. apply uc_res_int; assumption. }
  if_true. step. rewrite (uc_c_ltu (u32_at bs c) 4) by lia. if_false. step. step.
  rewrite (uc_c_eq_s32 (u32_at bs (c + 4)) 6) by lia.
  destruct (Z.eqb_spec (u32_at bs (c + 4)) 6) as [Ht6|Ht6].
  2: { if_true. eapply uc_neg1; [| intros k Hk; reflexivity | exact HFRM | exact FRM].
       rewrite <- HV. apply uc_res_bad; [exact Hu20 | right; split; assumption]. }
  (* Float (body.h:194-202) *)
  if_false.
  destruct (uc_bytes4 (c + 8) ltac:(lia) ltac:(lia)) as (b8 & b9 & b10 & b11 & B8 & B9 & B10 & B11 & EB).
  pose proof (uc_rd1 m (c + 8 + 1) b9 FRM ltac:(lia) B9) as HR. replace (P + (c + 8 + 1)) with (P + c + 9) in HR by lia.
  step. clear HR.
  pose proof (uc_rd1 m (c + 8) b8 FRM ltac:(lia) B8) as HR. replace (P + (c + 8)) with (P + c + 8) in HR by lia.
  step. clear HR.
  pose proof (uc_rd1 m (c + 8 + 2) b10 FRM ltac:(lia) B10) as HR. replace (P + (c + 8 + 2)) with (P + c + 10) in HR by lia.
  step. clear HR.
  pose proof (uc_rd1 m (c + 8 + 3) b11 FRM ltac:(lia) B11) as HR. replace (P + (c + 8 + 3)) with (P + c + 11) in HR by lia.
  step. clear HR.
  step. step. step. step. step. step. step.
  eapply (uc_flt (u32_at bs (c + 8))); [exact Hb | reflexivity | | reflexivity | | exact FRM].
  - rewrite EB. exact (uc_asm_word b8 b9 b10 b11).
  - rewrite <- HV. apply uc_res_flt; assumption.
Qed.

(** ** The Struct walk at 0x1475c (SPA_POD_STRUCT_FOREACH, iter.h:31-42, with the key pairing of
    reac_role_cfg.c:79-102): the params prop at offset rf with value size vs (body at rf + 16), the child at offset
    c, the key slot k (a0: 0, or the address of the key string at offset kk), n passes of fuel. s4 = vs - 8,
    s5 = the body, s6 = its end - 8. *)
Definition key_reg (k : option Z) : word :=
  match k with None => Z_to_bv 64 0 | Some kk => Z_to_bv 64 (P + kk) end.

(** The key slot: open, or the C string sx at offset kk of the pod, its NUL inside the pod. *)
Definition key_ok (k : option Z) (km : option (list byte)) : Prop :=
  match k, km with
  | None, None => True
  | Some kk, Some sx => 0 <= kk /\ kk + Z.of_nat (length sx) + 1 <= Z.of_nat (length bs) /\ ~ In NUL sx /\
                        firstn (S (length sx)) (skipn (Z.to_nat kk) bs) = sx ++ [NUL]
  | _, _ => False
  end.

(** *** The walk's words, bytes and key strings *)
Lemma ub_le_rt : forall l : list byte, Z_to_le_bytes (length l) (bytes_le_to_Z l) = l.
Proof.
  induction l as [|b l IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (byte_range b) as Hb. pose proof (le_bytes_nonneg l) as Hl.
  rewrite lor_low_shiftl by lia. f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8). change (2^8) with 256.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256. rewrite Z.div_add by lia.
    rewrite Z.div_small, Z.add_0_l by lia. exact IH.
Qed.

Lemma ub_rd4 : forall o, 0 <= o -> (Z.to_nat o + 4 <= length bs)%nat ->
  firstn 4 (skipn (Z.to_nat o) bs) = le4 (Z_to_bv 64 (u32_at bs o)).
Proof.
  intros o H0 H1. unfold le4, u32_at, rd32.
  pose proof (rd32_range (skipn (Z.to_nat o) bs)) as R. unfold rd32 in R.
  rewrite unsigned_lit by lia.
  assert (L : length (firstn 4 (skipn (Z.to_nat o) bs)) = 4%nat) by (rewrite length_firstn, length_skipn; lia).
  pose proof (ub_le_rt (firstn 4 (skipn (Z.to_nat o) bs))) as E. rewrite L in E. symmetry. exact E.
Qed.

Lemma ub_rd1 : forall (l : list byte) i, (i < length l)%nat -> firstn 1 (skipn i l) = [nth i l NUL].
Proof.
  induction l as [|x l IH]; intros i H; [cbn in H; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [skipn nth length] in *. apply IH. lia.
Qed.

Lemma ub_ld4 : forall m o, frame m -> 0 <= o -> o + 4 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (P + o)) 4 = Some (le4 (Z_to_bv 64 (u32_at bs o))).
Proof.
  intros m o FR H0 H1. rewrite (bytes_at_read rsegs m P bs o 4 (pod_at m FR) H0 ltac:(lia)).
  rewrite ub_rd4 by lia. reflexivity.
Qed.

Lemma ub_ld1 : forall m o, frame m -> 0 <= o -> o + 1 <= Z.of_nat (length bs) ->
  ov_read_bytes rsegs m (wa (P + o)) 1 = Some [nth (Z.to_nat o) bs NUL].
Proof.
  intros m o FR H0 H1. rewrite (bytes_at_read rsegs m P bs o 1 (pod_at m FR) H0 ltac:(lia)).
  rewrite ub_rd1 by lia. reflexivity.
Qed.

Lemma ub_sub : forall m o n, frame m -> 0 <= o -> (Z.to_nat o + n <= length bs)%nat ->
  bytes_at rsegs m (P + o) (firstn n (skipn (Z.to_nat o) bs)).
Proof.
  intros m o n FR H0 H1. pose proof (pod_at m FR) as B.
  rewrite <- (firstn_skipn (Z.to_nat o) bs) in B. apply bytes_at_app in B as [_ B].
  rewrite length_firstn, Nat.min_l in B by lia. rewrite Z2Nat.id in B by lia.
  rewrite <- (firstn_skipn n (skipn (Z.to_nat o) bs)) in B. apply bytes_at_app in B as [B _]. exact B.
Qed.

Lemma ub_nth_firstn : forall (l : list byte) n i, (i < n)%nat -> nth i (firstn n l) NUL = nth i l NUL.
Proof.
  induction l as [|x l IH]; intros n i H.
  - rewrite firstn_nil. reflexivity.
  - destruct n as [|n]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn [firstn nth]. apply IH. lia.
Qed.

Lemma ub_nth_skipn : forall (l : list byte) a i, nth i (skipn a l) NUL = nth (a + i) l NUL.
Proof.
  induction l as [|x l IH]; intros a i.
  - rewrite skipn_nil. destruct i as [|i]; destruct (a + _)%nat; reflexivity.
  - destruct a as [|a]; [reflexivity|]. cbn [skipn Nat.add nth]. apply IH.
Qed.

Lemma ub_nul_idx_le : forall (l : list byte) i, (i < length l)%nat -> bv_unsigned (nth i l NUL) = 0 ->
  (nul_idx l <= i)%nat.
Proof.
  induction l as [|x l IH]; intros i Hi H; cbn [length] in Hi; [lia|]. cbn [nul_idx].
  destruct (bv_unsigned x =? 0) eqn:E; [lia|].
  destruct i as [|i]; [cbn [nth] in H; apply Z.eqb_neq in E; contradiction|].
  cbn [nth] in H. specialize (IH i ltac:(lia) H). lia.
Qed.

Lemma ub_cstr_nul : forall l, (nul_idx l < length l)%nat -> firstn (S (nul_idx l)) l = cstr l ++ [NUL].
Proof.
  induction l as [|x l IH]; intros H; [cbn in H; lia|]. unfold cstr in *. cbn [nul_idx length] in *.
  destruct (bv_unsigned x =? 0) eqn:E.
  - cbn [firstn app]. f_equal. apply bv_eq. apply Z.eqb_eq in E. rewrite E. reflexivity.
  - cbn [firstn app]. f_equal. apply IH. lia.
Qed.

Lemma ub_cstr_nonul : forall l, ~ In NUL (cstr l).
Proof.
  induction l as [|x l IH]; unfold cstr in *; cbn [nul_idx]; [cbn; tauto|].
  destruct (bv_unsigned x =? 0) eqn:E; cbn [firstn In]; [tauto|]. intros [Hx|Hx].
  - subst x. vm_compute in E. discriminate E.
  - exact (IH Hx).
Qed.

(** spa_pod_get_string (body.h:224-237) of the child at c, as the walk tests it. *)
Lemma ub_gs : forall c, 0 <= c -> c + 8 + u32_at bs c <= Z.of_nat (length bs) ->
  spa_get_string (child_at bs c) =
  if (u32_at bs c <? 2^20) && (u32_at bs (c + 4) =? 8) && (1 <=? u32_at bs c) &&
     (bv_unsigned (nth (Z.to_nat (c + 8 + u32_at bs c - 1)) bs NUL) =? 0)
  then Some (cstr (firstn (Z.to_nat (u32_at bs c)) (skipn (Z.to_nat (c + 8)) bs))) else None.
Proof.
  intros c H0 H1. unfold spa_get_string, child_at, last_body_byte, SPA_POD_MAX_SIZE, POD_STRING.
  cbn [e_size e_type e_body].
  destruct (u32_at bs c <? 2^20), (u32_at bs (c + 4) =? 8); cbn [andb]; try reflexivity.
  destruct (1 <=? u32_at bs c) eqn:E1; cbn [andb]; [|reflexivity].
  apply Z.leb_le in E1.
  rewrite ub_nth_firstn by lia. rewrite ub_nth_skipn.
  replace (Z.to_nat (c + 8) + Z.to_nat (u32_at bs c - 1))%nat with (Z.to_nat (c + 8 + u32_at bs c - 1)) by lia.
  reflexivity.
Qed.

(** The key spa_pod_get_string gives is a C string at c + 8, its NUL inside the pod. *)
Lemma ub_key_ok : forall c, 0 <= c -> c + 8 + u32_at bs c <= Z.of_nat (length bs) -> 1 <= u32_at bs c ->
  bv_unsigned (nth (Z.to_nat (c + 8 + u32_at bs c - 1)) bs NUL) = 0 ->
  key_ok (Some (c + 8)) (Some (cstr (firstn (Z.to_nat (u32_at bs c)) (skipn (Z.to_nat (c + 8)) bs)))).
Proof.
  intros c H0 H1 H2 H3.
  remember (firstn (Z.to_nat (u32_at bs c)) (skipn (Z.to_nat (c + 8)) bs)) as body eqn:EB.
  assert (LB : length body = Z.to_nat (u32_at bs c)) by (subst body; rewrite length_firstn, length_skipn; lia).
  assert (NB : bv_unsigned (nth (Z.to_nat (u32_at bs c) - 1) body NUL) = 0).
  { subst body. rewrite ub_nth_firstn by lia. rewrite ub_nth_skipn.
    replace (Z.to_nat (c + 8) + (Z.to_nat (u32_at bs c) - 1))%nat with (Z.to_nat (c + 8 + u32_at bs c - 1)) by lia.
    exact H3. }
  pose proof (ub_nul_idx_le body (Z.to_nat (u32_at bs c) - 1) ltac:(lia) NB) as NI.
  assert (LC : length (cstr body) = nul_idx body).
  { unfold cstr. rewrite length_firstn. pose proof (nul_idx_le body). lia. }
  cbn [key_ok]. split; [lia|]. split; [rewrite LC; lia|]. split; [apply ub_cstr_nonul|].
  rewrite LC. rewrite <- ub_cstr_nul by lia. subst body.
  rewrite firstn_firstn. rewrite Nat.min_l by lia. reflexivity.
Qed.

Lemma ub_zx32 : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma ub_sx32_eqb : forall z, 0 <= z < 2^32 -> bv_eqb (sx32 (Z_to_bv 64 z)) (Z_to_bv 64 8) = (z =? 8).
Proof.
  intros z H. unfold sx32, bv_eqb. rewrite (unsigned_lit z) by lia. rewrite (unsigned_lit 8) by lia.
  rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  destruct (Z.eqb_spec z 8) as [->|E]; [reflexivity|]. apply Z.eqb_neq. Z.div_mod_to_equations. lia.
Qed.

Lemma ub_srl20 : forall z, 0 <= z < 2^32 -> bv_eqb (Z_to_bv 64 (Z.shiftr z 20)) (Z_to_bv 64 0) = (z <? 2^20).
Proof.
  intros z H. unfold bv_eqb. rewrite Z.shiftr_div_pow2 by lia.
  assert (D : 0 <= z / 2^20 < 2^64) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (unsigned_lit (z / 2^20)) by exact D. rewrite (unsigned_lit 0) by lia.
  destruct (Z.ltb_spec z (2^20)) as [L|L].
  - rewrite Z.div_small by lia. reflexivity.
  - apply Z.eqb_neq. assert (1 <= z / 2^20) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

(** The size shifted right by 20, once the size is below 2^20 (a0 after 0x14780). *)
Lemma ub_shr20_0 : forall z, 0 <= z < 2^20 -> Z.shiftr z 20 = 0.
Proof. intros z H. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

(** addiw of a small nonnegative value (0x14798). *)
Lemma ub_swrap_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z H. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  rewrite Z.mod_small by lia. lia.
Qed.

(** The all-ones mask of the branch-free string test (0x147c0). *)
Lemma ub_land_ones : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof.
  intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia.
  apply Z.mod_small. lia.
Qed.

Lemma ub_word_eqb0 : forall r : word, bv_eqb r (Z_to_bv 64 0) = true -> r = Z_to_bv 64 0.
Proof.
  intros r H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. rewrite H. reflexivity.
Qed.

Lemma ub_land3 : forall x, 0 <= x -> x mod 8 = 0 -> Z.land x 3 = 0.
Proof.
  intros x H0 H8. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. change (2^2) with 4.
  Z.div_mod_to_equations. lia.
Qed.

Lemma ub_lor7 : forall z, 0 <= z -> z + 7 <= Z.lor (z + 7) 7 <= z + 14 /\ Z.lor (z + 7) 7 + 1 = round_up8 (8 + z) /\
  (Z.lor (z + 7) 7 + 1) mod 8 = 0.
Proof.
  intros z H. unfold round_up8. replace (8 + z - 1) with (z + 7) by lia. rewrite lor7 by lia.
  split; [Z.div_mod_to_equations; lia|]. split; [reflexivity|].
  replace (8 * ((z + 7) / 8) + 7 + 1) with (((z + 7) / 8 + 1) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(** The guard of the walk (spa_pod_is_inside, iter.h:31-37) on a child offset c that is 0 mod 8. *)
Lemma ub_inside : forall rf vs c, rf + 16 <= c -> c mod 8 = 0 -> 8 <= vs ->
  pod_is_inside bs (rf + 16) vs c = (c - (rf + 16) <=? vs - 8) && (u32_at bs c <=? rf + 8 + vs - c).
Proof.
  intros rf vs c H1 H2 H3. unfold pod_is_inside, ptr_type_inside, ptrinside, ptr_remaining.
  replace (c mod 4) with 0 by (Z.div_mod_to_equations; lia).
  rewrite (proj2 (Z.leb_le (rf + 16) c) H1), (proj2 (Z.leb_le 8 vs) H3). cbn [Z.eqb andb].
  replace (rf + 16 + vs - (c + 8)) with (rf + 8 + vs - c) by lia. reflexivity.
Qed.

Lemma ub_mod16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. Z.div_mod_to_equations. lia. Qed.

Lemma ub_mod8_add2 : forall a b, a mod 8 = 0 -> b mod 8 = 0 -> (a + b) mod 8 = 0.
Proof. intros a b Ha Hb. rewrite Z.add_mod, Ha, Hb by lia. reflexivity. Qed.

Lemma ub_mod8_add3 : forall a b d, a mod 8 = 0 -> b mod 8 = 0 -> d mod 8 = 0 -> (a + (b + d)) mod 8 = 0.
Proof. intros a b d Ha Hb Hd. apply ub_mod8_add2; [exact Ha | apply ub_mod8_add2; assumption]. Qed.

(** A fact kept out of sight of lia. *)
Definition ub_hide (A : Prop) : Prop := A.

(** A branch whose condition the context decides. *)
Ltac ub_cond := unfold bv_eqb, bv_ltu, bv_lts, bv_leu;
  repeat match goal with |- context [bv_unsigned (Z_to_bv 64 ?e)] => rewrite (unsigned_lit e) by lia end;
  solve_cond_rec.
Ltac ub_go := lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
      first [ replace c with true; [cbv iota | symmetry; ub_cond]
            | replace c with false; [cbv iota | symmetry; ub_cond] ]
  end.
Ltac ub_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity]) end.
(** The comparisons of the branch-free string test (0x147a4-0x147c0), decided by the context. *)
Ltac ub_dec :=
  repeat match goal with
  | |- context [Z.ltb ?x ?y] => first [ rewrite (proj2 (Z.ltb_lt x y)) by lia | rewrite (proj2 (Z.ltb_ge x y)) by lia ]
  | |- context [bv_swrap 32 ?e] => rewrite (ub_swrap_small e) by lia
  | |- context [Z.land 18446744073709551615 ?x] => rewrite (ub_land_ones x) by lia
  | |- context [Z.land 0 ?x] => rewrite (Z.land_0_l x)
  end;
  try change (Z.b2z true) with 1; try change (Z.b2z false) with 0.

Lemma walk_loop : null = false -> forall rf vs, 16 <= rf -> rf mod 8 = 0 -> 8 <= vs < 2^20 ->
  rf + 16 + vs <= Z.of_nat (length bs) ->
  forall n c k km m
    (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  x8 = Z_to_bv 64 Q -> x9 = Z_to_bv 64 0x1032e -> w10 = key_reg k -> x18 = Z_to_bv 64 (P + c) ->
  x19 = Z_to_bv 64 8 -> x20 = Z_to_bv 64 (vs - 8) -> x21 = Z_to_bv 64 (P + rf + 16) ->
  x22 = Z_to_bv 64 (P + rf + 8 + vs) ->
  rf + 16 <= c -> c <= rf + 16 + vs + 7 -> c mod 8 = 0 -> (Z.to_nat (rf + 16 + vs - c) < n)%nat ->
  key_ok k km ->
  walk_res bs (rf + 16) vs c n km = RES ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x1475c) fc None m (seg_rom rsegs)).
Proof.
  intros HN rf vs Hrf Hrf8 Hvs Hlen n. induction n as [|n IH];
    intros c k km m x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
      E8 E9 E10 E18 E19 E20 E21 E22 Hc1 Hc2 Hc8 Hn HK HW FRM; [lia|].
  subst x8 x9 w10 x18 x19 x20 x21 x22.
  pose proof args_facts as (_ & _ & HP0 & HP16 & HPL & _ & _ & Hlo0 & Hsp & Hlosp).
  assert (HP8 : ub_hide (P mod 8 = 0)) by exact (ub_mod16_8 P HP16). clear HP16.
  change (ub_hide (rf mod 8 = 0)) in Hrf8. change (ub_hide (c mod 8 = 0)) in Hc8.
  change (ub_hide (Z.to_nat (rf + 16 + vs - c) < S n)%nat) in Hn.
  pose proof FRM as ((j & FR) & ST & MU & WM & MI).
  rewrite walk_res_step, (ub_inside rf vs c Hc1 Hc8 (proj1 Hvs)) in HW.
  (* the exits that return 0 through the epilogue (a1 = 0 at 0x148f0) *)
  assert (EXIT : forall (x1' y0' y1' y2' x8' x9' w10' w12' w13' w14' w15' w16' w17' x18' x19' x20' x21' x22' x23'
                         u3' u4' u5' u6' : word),
    RES = (None, 0) ->
    evt rsegs Post (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0' y1' y2' x8' x9' w10' (Z_to_bv 64 0)
                         w12' w13' w14' w15' w16' w17' x18' x19' x20' x21' x22' x23' s8 s9 s10 s11 u3' u4' u5' u6')
                    F (Z_to_bv 64 0x148f0) fc None m (seg_rom rsegs))).
  { intros x1' y0' y1' y2' x8' x9' w10' w12' w13' w14' w15' w16' w17' x18' x19' x20' x21' x22' x23' u3' u4' u5' u6' ER.
    eapply (epi m j F fc 0); [rewrite ER; reflexivity | intros; reflexivity | exact HFRM | exact FR | exact ST
                             | exact MI | exact WM | rewrite ER; exact MU]. }
  (* 0x1475c-0x14778: the guards of spa_pod_is_inside; the trap on a NULL child at 0x1476c is not taken *)
  step. zstep. ub_go.
  zstep. zstep.
  destruct (Z.le_gt_cases (c - (rf + 16)) (vs - 8)) as [D1|D1].
  2:{ ub_go. apply EXIT. rewrite (proj2 (Z.leb_gt _ _) D1) in HW. cbn [andb] in HW. symmetry. exact HW. }
  ub_go.
  zstep. ub_go.
  assert (RCS : 0 <= u32_at bs c < 2^32) by (unfold u32_at; apply rd32_range).
  pose proof (ub_ld4 m c FRM ltac:(lia) ltac:(lia)) as HR. unfold wa in HR.
  zstep. clear HR. rewrite (ub_zx32 (u32_at bs c) RCS).
  zstep. zstep.
  destruct (Z.le_gt_cases (u32_at bs c) (rf + 8 + vs - c)) as [D2|D2].
  2:{ ub_go. zstep. zstep. apply EXIT. rewrite (proj2 (Z.leb_le _ _) D1), (proj2 (Z.leb_gt _ _) D2) in HW.
      cbn [andb] in HW. symmetry. exact HW. }
  ub_go.
  rewrite (proj2 (Z.leb_le _ _) D1), (proj2 (Z.leb_le _ _) D2) in HW. cbn [andb] in HW.
  (* 0x147d8-0x147ec: the next child, c + SPA_ROUND_UP_N(8 + size, 8), then the next pass *)
  assert (ADV : forall (x1' y0' y1' y2' w10' w11' w12' w13' w14' w15' w16' w17' u3' u4' u5' u6' : word) k' km',
    w10' = key_reg k' -> key_ok k' km' ->
    walk_res bs (rf + 16) vs (c + round_up8 (8 + u32_at bs c)) n km' = RES ->
    evt rsegs Post (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0' y1' y2' (Z_to_bv 64 Q)
                         (Z_to_bv 64 0x1032e) w10' w11' w12' w13' w14' w15' w16' w17' (Z_to_bv 64 (P + c))
                         (Z_to_bv 64 8) (Z_to_bv 64 (vs - 8)) (Z_to_bv 64 (P + rf + 16)) (Z_to_bv 64 (P + rf + 8 + vs))
                         (Z_to_bv 64 (u32_at bs c)) s8 s9 s10 s11 u3' u4' u5' u6')
                    F (Z_to_bv 64 0x147d8) fc None m (seg_rom rsegs))).
  { intros x1' y0' y1' y2' w10' w11' w12' w13' w14' w15' w16' w17' u3' u4' u5' u6' k' km' E10' HK' HW'.
    subst w10'.
    destruct (ub_lor7 (u32_at bs c) (proj1 RCS)) as (L7 & L7e & L7m).
    zstep. zstep. zstep. zstep.
    replace (P + c + Z.lor (u32_at bs c + 7) 7 + 1) with (P + (c + round_up8 (8 + u32_at bs c))) by lia.
    zstep.
    rewrite (ub_land3 (P + (c + round_up8 (8 + u32_at bs c))))
      by (first [lia | apply ub_mod8_add3; [exact HP8 | exact Hc8 | rewrite <- L7e; exact L7m]]).
    zstep. ub_go.
    unfold ub_hide in Hn.
    eapply (IH (c + round_up8 (8 + u32_at bs c)) k' km' m).
    1-8: reflexivity.
    - lia.
    - lia.
    - apply ub_mod8_add2; [exact Hc8 | rewrite <- L7e; exact L7m].
    - lia.
    - exact HK'.
    - exact HW'.
    - exact FRM. }
  (* 0x147d4: the key slot is emptied *)
  assert (NEXT0 : forall (x1' y0' y1' y2' w10' w11' w12' w13' w14' w15' w16' w17' u3' u4' u5' u6' : word),
    walk_res bs (rf + 16) vs (c + round_up8 (8 + u32_at bs c)) n None = RES ->
    evt rsegs Post (MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0' y1' y2' (Z_to_bv 64 Q)
                         (Z_to_bv 64 0x1032e) w10' w11' w12' w13' w14' w15' w16' w17' (Z_to_bv 64 (P + c))
                         (Z_to_bv 64 8) (Z_to_bv 64 (vs - 8)) (Z_to_bv 64 (P + rf + 16)) (Z_to_bv 64 (P + rf + 8 + vs))
                         (Z_to_bv 64 (u32_at bs c)) s8 s9 s10 s11 u3' u4' u5' u6')
                    F (Z_to_bv 64 0x147d4) fc None m (seg_rom rsegs))).
  { intros x1' y0' y1' y2' w10' w11' w12' w13' w14' w15' w16' w17' u3' u4' u5' u6' HW'.
    zstep. eapply ADV with (k' := None) (km' := None); [reflexivity | exact I | exact HW']. }
  destruct k as [kk|]; destruct km as [sx|]; cbn [key_ok] in HK; try contradiction; cbn [key_reg].
  - (* a value slot: strcmp(key, "reac.cfg.role") at 0x147cc *)
    destruct HK as (Hk0 & Hk1 & Hk2 & Hk3). cbv iota beta in HW.
    zstep. ub_go.
    zstep. zstep.
    eapply evt_cut.
    { eapply HSTR with (sx := sx) (sy := ROLE_KEY).
      - rewrite unsigned_lit by lia.
        replace (sx ++ [Z_to_bv 8 0]) with (firstn (S (length sx)) (skipn (Z.to_nat kk) bs)) by exact Hk3.
        apply ub_sub; [exact FRM | exact Hk0 | lia].
      - exact Hk2.
      - rewrite unsigned_lit by lia. exact (lit_at m MI).
      - exact ROLE_KEY_nonul. }
    intros ms' (r & r11 & r12 & r13 & E & IFF). subst ms'. ub_ret.
    zstep.
    destruct (bv_eqb r (Z_to_bv 64 0)) eqn:ER; cbv iota.
    + apply ub_word_eqb0 in ER. apply IFF in ER. rewrite (proj2 (bytes_eqb_eq sx ROLE_KEY) ER) in HW.
      unfold ub_hide in Hc8.
      eapply (value_tail HN c m); [reflexivity | reflexivity | reflexivity | lia | exact Hc8 | lia | exact HW
                                  | exact FRM].
    + assert (NE : bytes_eqb sx ROLE_KEY = false).
      { destruct (bytes_eqb sx ROLE_KEY) eqn:EB; [|reflexivity]. apply bytes_eqb_eq, IFF in EB. subst r.
        unfold bv_eqb in ER. rewrite Z.eqb_refl in ER. discriminate ER. }
      rewrite NE in HW. apply NEXT0. exact HW.
  - (* the key slot: spa_pod_get_string at 0x14780-0x147c4 *)
    cbv iota beta in HW.
    zstep. ub_go.
    zstep. zstep. rewrite (ub_srl20 _ RCS).
    pose proof (ub_gs c ltac:(lia) ltac:(lia)) as GSE.
    destruct (Z.lt_ge_cases (u32_at bs c) (2^20)) as [B20|B20].
    2:{ ub_go. apply NEXT0. rewrite GSE, (proj2 (Z.ltb_ge _ _) B20) in HW. exact HW. }
    ub_go. rewrite (ub_shr20_0 (u32_at bs c)) by lia.
    zstep.
    destruct (Z.eq_dec (u32_at bs c) 0) as [B0|B0].
    { ub_go. eapply ADV with (k' := None) (km' := None); [reflexivity | exact I |].
      rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.leb_gt 1 (u32_at bs c)) ltac:(lia)), andb_false_r in HW.
      exact HW. }
    ub_go.
    assert (RCT : 0 <= u32_at bs (c + 4) < 2^32) by (unfold u32_at; apply rd32_range).
    pose proof (ub_ld4 m (c + 4) FRM ltac:(lia) ltac:(lia)) as HR. unfold wa in HR.
    replace (P + (c + 4)) with (P + c + 4) in HR by lia.
    zstep. clear HR.
    zstep. rewrite (ub_sx32_eqb _ RCT).
    destruct (Z.eq_dec (u32_at bs (c + 4)) 8) as [T8|T8].
    2:{ ub_go. eapply ADV with (k' := None) (km' := None); [reflexivity | exact I |].
        rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.eqb_neq _ _) T8) in HW. exact HW. }
    ub_go.
    (* 0x14794-0x147b0: a0 = the body, a1 = its last byte's address; both traps are not taken *)
    zstep. zstep. ub_dec.
    zstep. zstep. ub_go.
    zstep. ub_dec. zstep. ub_dec. zstep. zstep. ub_go.
    (* 0x147b4-0x147c4: a0 = (last byte = 0) ? body : 0 *)
    pose proof (ub_ld1 m (c + 8 + u32_at bs c - 1) FRM ltac:(lia) ltac:(lia)) as HR. unfold wa in HR.
    replace (P + (c + 8 + u32_at bs c - 1)) with (P + c + 8 + (u32_at bs c + -1)) in HR by lia.
    zstep. clear HR.
    zstep. pose proof (byte_range (nth (Z.to_nat (c + 8 + u32_at bs c - 1)) bs NUL)) as BR.
    destruct (Z.eq_dec (bv_unsigned (nth (Z.to_nat (c + 8 + u32_at bs c - 1)) bs NUL)) 0) as [L0|L0].
    + ub_dec. zstep. zstep. ub_dec. zstep.
      eapply ADV with (k' := Some (c + 8))
                      (km' := Some (cstr (firstn (Z.to_nat (u32_at bs c)) (skipn (Z.to_nat (c + 8)) bs)))).
      * cbn [key_reg]. f_equal. lia.
      * apply ub_key_ok; lia.
      * rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.eqb_eq _ _) T8),
          (proj2 (Z.leb_le 1 (u32_at bs c)) ltac:(lia)), (proj2 (Z.eqb_eq _ _) L0) in HW. exact HW.
    + ub_dec. zstep. zstep. ub_dec. zstep.
      eapply ADV with (k' := None) (km' := None); [reflexivity | exact I |].
      rewrite GSE, (proj2 (Z.ltb_lt _ _) B20), (proj2 (Z.eqb_eq _ _) T8),
        (proj2 (Z.leb_le 1 (u32_at bs c)) ltac:(lia)), (proj2 (Z.eqb_neq _ _) L0) in HW. exact HW.
Qed.

(** *** The exits to the epilogue and the found prop *)
Lemma ua_exit : forall m rc (x1 y0 y1 y2 x8 x9 w10 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  RES = (None, rc) -> frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 (Z_to_bv 64 rc)
                       w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x148f0) fc None m (seg_rom rsegs)).
Proof.
  intros m rc x1 y0 y1 y2 x8 x9 w10 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    ER ((j & FR) & ST & MU & WM & MI).
  eapply epi; [rewrite ER; reflexivity | intros k _; reflexivity | exact HFRM | exact FR | exact ST | exact MI
              | exact WM |].
  rewrite ER. exact MU.
Qed.

(** 0x147f0: a1 = 0, then the epilogue. *)
Lemma ua_147f0 : forall m (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  RES = (None, 0) -> frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x147f0) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 ER FRM.
  zstep. zstep. apply ua_exit; [exact ER | exact FRM].
Qed.

(** 0x148ec: a1 = -1, then the epilogue. *)
Lemma ua_148ec : forall m (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  RES = (None, -1) -> frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x148ec) fc None m (seg_rom rsegs)).
Proof.
  intros m x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 ER FRM.
  zstep. apply ua_exit; [exact ER | exact FRM].
Qed.

(** 0x14718: the params prop at offset r was found (its address in a2); the R & 3 trap (not taken: r mod 8 = 0),
    spa_pod_is_struct of its value (size in s6), the walk setup 0x14734-0x14758, then the Struct walk. *)
Lemma ua_found : null = false -> is_object_type bs POD_OBJECT_PROPS = true ->
  forall r m (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  x8 = Z_to_bv 64 Q -> w12 = Z_to_bv 64 (P + r) -> x22 = sx32 (Z_to_bv 64 (u32_at bs (r + 8))) ->
  16 <= r -> r mod 8 = 0 -> r + 16 + u32_at bs (r + 8) <= Z.of_nat (length bs) ->
  find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs) = Some r ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x14718) fc None m (seg_rom rsegs)).
Proof.
  intros HN HOBJ r m x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6
    E8 E12 E22 Hr1 Hr3 Hend HF FRM.
  subst x8 w12 x22.
  pose proof args_facts as (L8 & HS & P0 & P16 & HPL & Q4 & SQ & LO0 & SP64 & HL).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (ua_u32 (r + 8)) as Rv. pose proof (ua_u32 (r + 12)) as Rt.
  pose proof (parse_model_found bs r HOBJ HF) as EM.
  remember (u32_at bs (r + 8)) as vs eqn:Evs.
  zstep. (* andi a0,a2,3 *)
  zstep. ua_go false. (* bnez a0: the trap, not taken *)
  zstep. rewrite (ua_srliw_sx vs) by lia. (* srliw a0,s6,20 *)
  zstep. (* bnez a0 *)
  destruct (Z_lt_le_dec vs 1048576) as [V20|V20].
  2:{ ua_go true. apply ua_147f0; [|exact FRM]. rewrite (ua_res HN), EM.
      replace (is_struct_at bs (r + 8)) with false; [reflexivity|].
      rewrite ua_is_struct, <- Evs, (proj2 (Z.ltb_ge _ _) V20). reflexivity. }
  ua_go false. rewrite (ua_sx32 vs) by lia.
  pose proof (ua_rd m (r + 12) FRM ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a0,12(a2) *)
  zstep. (* li a1,14 *)
  zstep. rewrite (ua_eqb_sx (u32_at bs (r + 12)) 14) by lia. (* bne a0,a1 *)
  destruct (Z.eq_dec (u32_at bs (r + 12)) 14) as [T14|T14].
  2:{ ua_go true. apply ua_147f0; [|exact FRM]. rewrite (ua_res HN), EM.
      replace (is_struct_at bs (r + 8)) with false; [reflexivity|].
      rewrite ua_is_struct, <- Evs. replace (r + 8 + 4) with (r + 12) by lia.
      rewrite (proj2 (Z.ltb_lt _ _) V20), (proj2 (Z.eqb_neq _ _) T14). reflexivity. }
  ua_go false.
  assert (IS : is_struct_at bs (r + 8) = true).
  { rewrite ua_is_struct, <- Evs. replace (r + 8 + 4) with (r + 12) by lia.
    rewrite (proj2 (Z.ltb_lt _ _) V20), (proj2 (Z.eqb_eq _ _) T14). reflexivity. }
  rewrite IS in EM.
  zstep. (* li s3,8 *)
  zstep. (* bltu s6,s3 *)
  destruct (Z_lt_le_dec vs 8) as [V8|V8].
  { ua_go true. apply ua_147f0; [|exact FRM]. rewrite (ua_res HN), EM. cbv iota.
    destruct (length bs) as [|n0] eqn:EL; [lia|]. apply ua_walk_small. exact V8. }
  ua_go false.
  do 8 zstep. (* mv a0,zero; addi a2; addi s4; addi s5; add s6; auipc; addi s1; mv s2 *)
  eapply (walk_loop HN r vs Hr1 Hr3 ltac:(lia) ltac:(lia) (length bs) (r + 16) None None m).
  1-8: ua_eq.
  1-4: ua_lia.
  - exact I.
  - rewrite (ua_res HN), EM. reflexivity.
  - exact FRM.
Qed.

(** ** The find loop at 0x146d0 (spa_pod_object_find_prop, iter.h:255-258, with spa_pod_prop_is_inside): the prop at
    offset r, n passes of fuel. a0 = P + 8 (the object body), a3 = S - 16, a4 = P + S - 8, a5 = SPA_PROP_params. *)
Lemma find_loop : null = false -> is_object_type bs POD_OBJECT_PROPS = true -> 16 <= u32_at bs 0 ->
  forall n r m (x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23 u3 u4 u5 u6 : word),
  x8 = Z_to_bv 64 Q -> w10 = Z_to_bv 64 (P + 8) -> w12 = Z_to_bv 64 (P + r) ->
  w13 = Z_to_bv 64 (u32_at bs 0 - 16) -> w14 = Z_to_bv 64 (P + u32_at bs 0 - 8) -> w15 = Z_to_bv 64 0x80001 ->
  16 <= r -> r <= u32_at bs 0 + 15 -> r mod 8 = 0 -> (Z.to_nat (8 + u32_at bs 0 - r) < n)%nat ->
  find_prop bs (u32_at bs 0) POD_PROP_PARAMS r n = find_prop bs (u32_at bs 0) POD_PROP_PARAMS 16 (length bs) ->
  frame m ->
  evt rsegs Post (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17
                       x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 u3 u4 u5 u6)
                  F (Z_to_bv 64 0x146d0) fc None m (seg_rom rsegs)).
Proof.
  intros HN HOBJ H16.
  pose proof args_facts as (L8 & HS & P0 & P16 & HPL & Q4 & SQ & LO0 & SP64 & HL).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (ua_u32 0) as R0.
  induction n as [|n IH]; intros r m x1 y0 y1 y2 x8 x9 w10 w11 w12 w13 w14 w15 w16 w17 x18 x19 x20 x21 x22 x23
    u3 u4 u5 u6 E8 E10 E12 E13 E14 E15 Hr1 Hr2 Hr3 Hn HF FRM; [lia|].
  subst x8 w10 w12 w13 w14 w15.
  assert (Hr4 : r mod 4 = 0) by ua_lia.
  zstep. (* mv a1,zero *)
  zstep. ua_go false. (* bltu a2,a0 *)
  zstep. (* sub a6,a2,a0 *)
  zstep. (* bltu a3,a6 *)
  destruct (Z_lt_le_dec (u32_at bs 0 - 16) (r - 8)) as [HB|HB].
  { ua_go true. apply ua_exit; [|exact FRM]. rewrite (ua_res HN). apply parse_model_no_params; [exact HOBJ|].
    rewrite <- HF. apply ua_fp_out. rewrite ua_pin by lia.
    rewrite (proj2 (Z.leb_gt _ _) HB). destruct (16 <=? u32_at bs 0); reflexivity. }
  ua_go false.
  pose proof (ua_u32 (r + 8)) as Rv. pose proof (ua_u32 r) as Rk.
  pose proof (ua_rd m (r + 8) FRM ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw s6,8(a2) *)
  remember (u32_at bs (r + 8)) as vs eqn:Evs.
  zstep. (* sub a6,a4,a2 *)
  zstep. (* slli a1,s6,32 *)
  zstep. rewrite (ua_sxmod vs) by lia. (* srli a1,a1,32 *)
  zstep. (* bltu a6,a1 *)
  destruct (Z_lt_le_dec (u32_at bs 0 - 8 - r) vs) as [HV|HV].
  { ua_go true. apply ua_147f0; [|exact FRM]. rewrite (ua_res HN). apply parse_model_no_params; [exact HOBJ|].
    rewrite <- HF. apply ua_fp_out. rewrite ua_pin by lia. rewrite <- Evs.
    assert (HV' : 8 + u32_at bs 0 - (r + 16) < vs) by lia.
    rewrite (proj2 (Z.leb_gt _ _) HV'), andb_false_r. reflexivity. }
  ua_go false.
  assert (PI : prop_is_inside bs 8 (u32_at bs 0) r = true).
  { rewrite ua_pin by lia. rewrite <- Evs.
    assert (HV' : vs <= 8 + u32_at bs 0 - (r + 16)) by lia.
    rewrite (proj2 (Z.leb_le _ _) H16), (proj2 (Z.leb_le _ _) HB), (proj2 (Z.leb_le _ _) HV'). reflexivity. }
  rewrite (ua_fp_in _ _ _ _ PI) in HF. rewrite <- Evs in HF.
  pose proof (ua_rd m r FRM ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a6,0(a2) *)
  zstep. rewrite (ua_eqb_sx (u32_at bs r) 524289) by lia. (* beq a6,a5 *)
  destruct (Z.eq_dec (u32_at bs r) 524289) as [K|K].
  { ua_go true. subst vs.
    eapply (ua_found HN HOBJ r m); [reflexivity | reflexivity | reflexivity | exact Hr1 | exact Hr3 | lia | | exact FRM].
    rewrite <- HF. rewrite (proj2 (Z.eqb_eq (u32_at bs r) POD_PROP_PARAMS) K). reflexivity. }
  ua_go false.
  rewrite (proj2 (Z.eqb_neq (u32_at bs r) POD_PROP_PARAMS) K) in HF.
  pose proof (ua_ru_facts vs ltac:(lia)) as (RU1 & RU2).
  zstep. (* addi a1,a1,15 *)
  zstep. rewrite (ua_ru vs). (* ori a1,a1,7 *)
  zstep. (* add a1,a2,a1 *)
  zstep. (* addi a2,a1,1 *)
  zstep. (* andi a1,a2,3 *)
  zstep. ua_go false. (* bnez a1 *)
  zstep. (* j 0x146d0 *)
  eapply (IH (r + round_up8 (16 + vs)) m).
  1-6: ua_eq.
  1-4: ua_lia.
  - exact HF.
  - exact FRM.
Qed.

(** 0x14648 on any memory m0 that the call has not changed outside the frame: the prologue (the frame carved from the
    stack), the NULL test (to 0x148ec), the P & 3 trap (not taken: P mod 16 = 0), spa_pod_is_object_type, the find
    setup, then the find loop. *)
Lemma ua_entry : forall m0 (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  stk rsegs m0 lo (bv_unsigned sp) -> mem_inv rsegs m0 ->
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] mi m0 -> wmono rsegs mi m0 ->
  evt rsegs Post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if null then 0 else P)) (Z_to_bv 64 Q)
                       a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x14648) fc None m0 (seg_rom rsegs)).
Proof.
  intros m0 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ST MI MU WM.
  pose proof args_facts as (L8 & HS & P0 & P16 & HPL & Q4 & SQ & LO0 & SP64 & HL).
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (ua_u32 0) as R0. pose proof (ua_u32 4) as R4. pose proof (ua_u32 8) as R8.
  carve_frame 80%nat ST.
  do 10 zstep. (* the frame: addi sp, nine sd *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jj :: _) => set (j0 := jj) in FR; clearbody j0 end.
  assert (FRM : frame m1).
  { split; [exists j0; exact FR|]. split; [exact ST|]. split; [exact MU|]. split; [exact WM | exact MI]. }
  clear FR ST MU WM MI.
  destruct null eqn:EN; cbv iota.
  { zstep. ua_go true. (* beqz a0: NULL *)
    apply ua_148ec; [|exact FRM]. unfold RES, parse_res. rewrite EN. reflexivity. }
  zstep. ua_go false. (* beqz a0 *)
  zstep. (* mv s0,a1 *)
  zstep. (* andi a1,a0,3 *)
  zstep. ua_go false. (* bnez a1: the trap, not taken *)
  pose proof (ua_rd m1 0 FRM ltac:(lia) ltac:(lia)) as RD. rewrite Z.add_0_r in RD.
  zstep. clear RD. (* lw a3,0(a0) *)
  zstep. rewrite (ua_srliw_sx (u32_at bs 0)) by lia. (* srliw a1,a3,20 *)
  zstep. (* bnez a1 *)
  destruct (Z_lt_le_dec (u32_at bs 0) 1048576) as [S20|S20].
  2:{ ua_go true. apply ua_148ec; [|exact FRM]. rewrite (ua_res EN). apply parse_model_not_props.
      rewrite ua_obj, (proj2 (Z.ltb_ge _ _) S20). reflexivity. }
  ua_go false. rewrite (ua_sx32 (u32_at bs 0)) by lia.
  zstep. (* li a1,8 *)
  zstep. (* bltu a3,a1 *)
  destruct (Z_lt_le_dec (u32_at bs 0) 8) as [S8|S8].
  { ua_go true. apply ua_148ec; [|exact FRM]. rewrite (ua_res EN). apply parse_model_not_props.
    rewrite ua_obj, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.leb_gt _ _) S8).
    destruct (u32_at bs 4 =? 15); reflexivity. }
  ua_go false.
  pose proof (ua_rd m1 4 FRM ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a1,4(a0) *)
  zstep. (* li a2,15 *)
  zstep. rewrite (ua_eqb_sx (u32_at bs 4) 15) by lia. (* bne a1,a2 *)
  destruct (Z.eq_dec (u32_at bs 4) 15) as [T15|T15].
  2:{ ua_go true. apply ua_148ec; [|exact FRM]. rewrite (ua_res EN). apply parse_model_not_props.
      rewrite ua_obj, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.eqb_neq _ _) T15). reflexivity. }
  ua_go false.
  pose proof (ua_rd m1 8 FRM ltac:(lia) ltac:(lia)) as RD.
  zstep. clear RD. (* lw a1,8(a0) *)
  zstep. zstep. (* lui a2,0x40; addiw a2,a2,2 *)
  zstep. rewrite (ua_eqb_sx (u32_at bs 8) 262146) by lia. (* bne a1,a2 *)
  destruct (Z.eq_dec (u32_at bs 8) 262146) as [O2|O2].
  2:{ ua_go true. apply ua_148ec; [|exact FRM]. rewrite (ua_res EN). apply parse_model_not_props.
      rewrite ua_obj, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.eqb_eq _ _) T15), (proj2 (Z.leb_le _ _) S8),
        (proj2 (Z.eqb_neq _ _) O2). reflexivity. }
  ua_go false.
  assert (HOBJ : is_object_type bs POD_OBJECT_PROPS = true).
  { rewrite ua_obj, (proj2 (Z.ltb_lt _ _) S20), (proj2 (Z.eqb_eq _ _) T15), (proj2 (Z.leb_le _ _) S8),
      (proj2 (Z.eqb_eq _ _) O2). reflexivity. }
  zstep. (* li a1,16 *)
  zstep. (* bltu a3,a1 *)
  destruct (Z_lt_le_dec (u32_at bs 0) 16) as [S16|S16].
  { ua_go true. apply ua_147f0; [|exact FRM]. rewrite (ua_res EN). apply parse_model_no_params; [exact HOBJ|].
    destruct (length bs) as [|n0] eqn:EL; [lia|]. apply ua_fp_out.
    rewrite ua_pin by lia. rewrite (proj2 (Z.leb_gt _ _) S16). reflexivity. }
  ua_go false.
  do 6 zstep. (* addi a0; addi a3; lui a5; addi a2; add a4; addiw a5 *)
  eapply (find_loop EN HOBJ ltac:(lia) (length bs) 16 m1).
  1-6: ua_eq.
  1-4: ua_lia.
  - reflexivity.
  - exact FRM.
Qed.

(** ** The whole body from 0x14648, NULL argument included. *)
Lemma walk : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evt rsegs Post (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (if null then 0 else P)) (Z_to_bv 64 Q)
                       a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 REAC_ROLE_PROP_PARSE) fc None mi (seg_rom rsegs)).
Proof.
  intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  unfold REAC_ROLE_PROP_PARSE.
  apply ua_entry; [exact HSTK | exact HMI | apply munch_refl | apply wmono_refl].
Qed.

End W.

Theorem reac_role_prop_parse_holds : strcmp_contract -> reac_role_prop_parse_contract.
Proof.
  intros HSTR. unfold reac_role_prop_parse_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m null lo P Q bs E0 E1 HARGS HSTK HLO HNOROM HFRM HMI.
  subst a0 a1.
  eapply walk with (ra := ra) (sp := sp) (gp := gp) (tp := tp) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3)
    (s4 := s4) (s5 := s5) (s6 := s6) (s7 := s7) (s8 := s8) (s9 := s9) (s10 := s10) (s11 := s11) (F := F)
    (fc := fc) (mi := m) (null := null) (lo := lo) (P := P) (Q := Q) (bs := bs); eassumption.
Qed.
