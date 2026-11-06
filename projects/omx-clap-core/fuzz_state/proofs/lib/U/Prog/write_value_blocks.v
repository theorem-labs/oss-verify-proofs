From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition WRITE_VALUE : Z := 0x14d8c.
Definition WV_FRAME : Z := 128.
Definition WV_PUT : Z := 0x150bc.
Definition WV_PUT_STRING : Z := 0x15e7c.
Definition WV_INDENT : Z := 0x16060.
Definition WV_STRLEN : Z := 0x21340.

Definition WV_R_OPEN : Z := 0x14e30.
Definition WV_R_STRLEN : Z := 0x1503c.
Definition WV_R_COMMA : Z := 0x14e98.
Definition WV_R_INDENT : Z := 0x14eac.
Definition WV_R_KEY : Z := 0x14ef0.
Definition WV_R_SEP : Z := 0x14f00.
Definition WV_R_ITEM : Z := 0x14f4c.
Definition WV_R_CLOSE : Z := 0x14f74.

Definition WV_S_NULL : Z := 0x102fe.
Definition WV_S_FALSE : Z := 0x10298.
Definition WV_S_TRUE : Z := 0x1033c.
Definition WV_S_ZERO : Z := 0x10378.
Definition WV_S_EMPTY : Z := 0x102f5.
Definition WV_S_LBRACKET : Z := 0x10334.
Definition WV_S_LBRACE : Z := 0x103f6.
Definition WV_S_RBRACKET : Z := 0x10368.
Definition WV_S_RBRACE : Z := 0x102a8.
Definition WV_S_COMMA : Z := 0x10336.
Definition WV_S_COLON : Z := 0x10341.
Definition WV_S_COLON_SP : Z := 0x103cc.

Definition wv_nz (a d : Z) : Z := if a =? 0 then d else a.
Definition wv_open (ty : Z) : Z := if ty =? 6 then WV_S_LBRACE else WV_S_LBRACKET.
Definition wv_close (ty : Z) : Z := if ty =? 6 then WV_S_RBRACE else WV_S_RBRACKET.
Definition wv_sep (pretty : Z) : Z := if pretty =? 0 then WV_S_COLON else WV_S_COLON_SP.
Definition wv_seplen (pretty : Z) : Z := if pretty =? 0 then 1 else 2.

Definition wv_node (m : word -> option byte) (v ty str kids keys n : Z) (pa pb : list byte) : Prop :=
  rw_cells rsegs m v [C4 (Z_to_bv 64 ty); CB 12 pa; C8 (Z_to_bv 64 str); C8 (Z_to_bv 64 kids);
                      C8 (Z_to_bv 64 keys); C8 (Z_to_bv 64 n); CB 8 pb].

Definition wv_frame (m : word -> option byte) (sp : word) (junk : list byte) (d : word) (c16 : cell)
  (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  rw_cells rsegs m (bv_unsigned sp - WV_FRAME)
    [CB 8 junk; C8 d; c16; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0;
     C8 ra].

Definition wv_inside (sp : word) (lo : Z) (m m' : word -> option byte) (junk : list byte) (d : word) (c16 : cell)
  (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
  stk rsegs m' lo (bv_unsigned sp - WV_FRAME) /\ wv_frame m' sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

Definition wv_exit (pc : word) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32) (lo : Z) (m : word -> option byte) (R : word -> word -> word -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F pc fc None m' (seg_rom rsegs) /\
    R a0 a1 a2 /\ munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
    mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp).

Definition wv_ls (pc : Z) (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word)
  (fc : bv 32) (o v pretty depth i : Z) (m : word -> option byte) : machine_state :=
  MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v)
        a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 56) (Z_to_bv 64 pretty) (Z_to_bv 64 0)
        (Z_to_bv 64 (depth + 1)) (Z_to_bv 64 (wv_seplen pretty)) (Z_to_bv 64 WV_S_COMMA) (Z_to_bv 64 (56 * i))
        (Z_to_bv 64 (8 * i)) (Z_to_bv 64 i) (Z_to_bv 64 6) t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom rsegs).

Ltac wv_unfold :=
  unfold WRITE_VALUE, WV_FRAME, WV_PUT, WV_PUT_STRING, WV_INDENT, WV_STRLEN, WV_R_OPEN, WV_R_STRLEN, WV_R_COMMA,
    WV_R_INDENT, WV_R_KEY, WV_R_SEP, WV_R_ITEM, WV_R_CLOSE, WV_S_NULL, WV_S_FALSE, WV_S_TRUE, WV_S_ZERO,
    WV_S_EMPTY, WV_S_LBRACKET, WV_S_LBRACE, WV_S_RBRACKET, WV_S_RBRACE, WV_S_COMMA, WV_S_COLON,
    WV_S_COLON_SP in *.

Lemma wv_sx32 : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x Hx. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply bv_swrap_small.
  assert (E : bv_half_modulus 32 = 2^31) by reflexivity. rewrite E. lia.
Qed.

Lemma wv_badty : forall ty, 6 < ty < 2^32 -> bv_ltu (Z_to_bv 64 6) (sx32 (Z_to_bv 64 ty)) = true.
Proof.
  intros ty Hty. unfold bv_ltu, sx32. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap. change (bv_modulus 64) with (2^64). change (bv_half_modulus 32) with (2^31).
  change (bv_modulus 32) with (2^32). apply Z.ltb_lt. Z.div_mod_to_equations. lia.
Qed.

Lemma wv_swrap : forall z, -2^31 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small. assert (E : bv_half_modulus 32 = 2^31) by reflexivity. rewrite E. lia.
Qed.

Lemma wv_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma wv_shr : forall i k, 0 <= k -> 0 <= i < 2^k -> Z.shiftr i k = 0.
Proof. intros i k Hk Hi. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.

Theorem wv_epi_put : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (lo : Z) (m0 m : word -> option byte) (junk : list byte) (d : word) (c16 : cell)
  (ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word),
  munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  lo + WV_FRAME <= bv_unsigned sp -> stk rsegs m lo (bv_unsigned sp - WV_FRAME) ->
  wv_frame m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  ((exists j, c16 = CB 8 j) \/ (exists w, c16 = C8 w)) ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
               (fun x0 x1 x2 => x0 = a0 /\ x1 = a1 /\ x2 = a2))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7
           g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6) F (Z_to_bv 64 0x1507c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 m junk d c16
    ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 MU WM MI LO ST FR C16.
  unfold wv_frame, wv_exit in *. wv_unfold.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  destruct C16 as [[j ->]|[w ->]];
  (do 14 zstep;
   replace (bv_unsigned sp - 128 + 128) with (bv_unsigned sp) by lia;
   rewrite Z_to_bv_bv_unsigned;
   release_frame FR ST (bv_unsigned sp); zstep;
   apply evt_done; do 16 eexists; split; [reflexivity|];
   split; [repeat split|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|exact ST]).
Qed.

Theorem wv_epi_ps : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (lo : Z) (m0 m : word -> option byte) (junk : list byte) (d : word) (c16 : cell)
  (ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word),
  munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  lo + WV_FRAME <= bv_unsigned sp -> stk rsegs m lo (bv_unsigned sp - WV_FRAME) ->
  wv_frame m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  ((exists j, c16 = CB 8 j) \/ (exists w, c16 = C8 w)) ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT_STRING) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
               (fun x0 x1 _ => x0 = a0 /\ x1 = a1))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7
           g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6) F (Z_to_bv 64 0x14fa0) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 m junk d c16
    ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 MU WM MI LO ST FR C16.
  unfold wv_frame, wv_exit in *. wv_unfold.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  destruct C16 as [[j ->]|[w ->]];
  (do 14 zstep;
   replace (bv_unsigned sp - 128 + 128) with (bv_unsigned sp) by lia;
   rewrite Z_to_bv_bv_unsigned;
   release_frame FR ST (bv_unsigned sp); zstep;
   apply evt_done; do 16 eexists; split; [reflexivity|];
   split; [repeat split|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|exact ST]).
Qed.

Theorem wv_epi_ret : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (lo : Z) (m0 m : word -> option byte) (junk : list byte) (d : word) (c16 : cell)
  (ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word),
  munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  lo + WV_FRAME <= bv_unsigned sp -> stk rsegs m lo (bv_unsigned sp - WV_FRAME) ->
  wv_frame m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  ((exists j, c16 = CB 8 j) \/ (exists w, c16 = C8 w)) ->
  evt rsegs (wv_exit (ret_pc ra) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 (fun _ _ _ => True))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7
           g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6) F (Z_to_bv 64 0x14fdc) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0 m junk d c16
    ra1 t0 t1 t2 g8 g9 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 MU WM MI LO ST FR C16.
  unfold wv_frame, wv_exit in *. wv_unfold.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (Hlo & _ & _).
  destruct C16 as [[j ->]|[w ->]];
  (do 14 zstep;
   replace (bv_unsigned sp - 128 + 128) with (bv_unsigned sp) by lia;
   rewrite Z_to_bv_bv_unsigned;
   release_frame FR ST (bv_unsigned sp); zstep;
   apply evt_done; do 16 eexists; split; [reflexivity|];
   split; [exact I|]; split; [exact MU|]; split; [exact WM|]; split; [exact MI|exact ST]).
Qed.

Lemma wv_lxor_ltb : forall a b, 0 <= a < 2^63 -> 0 <= b < 2^63 ->
  (Z.lxor a 9223372036854775808 <? Z.lxor b 9223372036854775808) = (a <? b).
Proof.
  intros a b Ha Hb. change 9223372036854775808 with (2^63).
  rewrite !zb_lxor_sign by lia. rewrite !Z.mod_small by lia.
  apply eq_true_iff_eq. rewrite !Z.ltb_lt. lia.
Qed.

Lemma wv_signed : forall x, 0 <= x < 2^63 -> bv_signed (Z_to_bv 64 x) = x.
Proof.
  intros x Hx. unfold bv_signed. rewrite unsigned_lit by lia. apply bv_swrap_small.
  assert (E : bv_half_modulus 64 = 2^63) by reflexivity. rewrite E. lia.
Qed.

Ltac uwv_pro :=
  do 16 zstep;
  let BV := fresh "BV" in
  if_cases BV; zify_cond BV; [exfalso; lia|];
  do 4 zstep;
  match goal with |- context [Z.land ?x 7] => rewrite (wv_land7 x) by (Z.div_mod_to_equations; lia) end;
  if_false;
  zstep.

Theorem wv_bad_type : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth ty str kids keys n : Z)
  (pa pb : list byte),
  mem_inv rsegs m -> wv_node m v ty str kids keys n pa pb -> 6 < ty < 2^32 -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs (wv_exit (ret_pc ra) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (fun _ _ _ => True))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth ty str kids keys n pa pb MI ND HT HV HA ST LO DV.
  unfold wv_node in ND. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  carve_frame 128%nat ST.
  uwv_pro.
  do 2 zstep.
  if_true_by (wv_badty ty HT).
  eapply wv_epi_ret; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR |
                      left; eexists; reflexivity].
Qed.

Theorem wv_null : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  mem_inv rsegs m -> wv_node m v 0 str kids keys n pa pb -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 WV_S_NULL /\ x2 = Z_to_bv 64 4))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb MI ND HV HA ST LO DV.
  unfold wv_node in ND. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  carve_frame 128%nat ST.
  uwv_pro.
  rewrite wv_sx32 by lia.
  do 2 zstep. if_false.
  do 8 zstep.
  do 5 zstep.
  eapply wv_epi_put; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR |
                      left; eexists; reflexivity].
Qed.

Theorem wv_false : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  mem_inv rsegs m -> wv_node m v 1 str kids keys n pa pb -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 WV_S_FALSE /\ x2 = Z_to_bv 64 5))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb MI ND HV HA ST LO DV.
  unfold wv_node in ND. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  carve_frame 128%nat ST.
  uwv_pro.
  rewrite wv_sx32 by lia.
  do 2 zstep. if_false.
  do 8 zstep.
  do 5 zstep.
  eapply wv_epi_put; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR |
                      left; eexists; reflexivity].
Qed.

Theorem wv_true : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  mem_inv rsegs m -> wv_node m v 2 str kids keys n pa pb -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 WV_S_TRUE /\ x2 = Z_to_bv 64 4))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb MI ND HV HA ST LO DV.
  unfold wv_node in ND. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  carve_frame 128%nat ST.
  uwv_pro.
  rewrite wv_sx32 by lia.
  do 2 zstep. if_false.
  do 8 zstep.
  do 6 zstep.
  eapply wv_epi_put; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR |
                      left; eexists; reflexivity].
Qed.

Theorem wv_str : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  mem_inv rsegs m -> wv_node m v 4 str kids keys n pa pb -> 0 < v -> v mod 8 = 0 -> 0 <= str < 2^64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT_STRING) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 _ => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 (wv_nz str WV_S_EMPTY)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb MI ND HV HA HS ST LO DV.
  unfold wv_node in ND. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  carve_frame 128%nat ST.
  uwv_pro.
  rewrite wv_sx32 by lia.
  do 2 zstep. if_false.
  do 10 zstep.
  if_cases B; zify_cond B.
  - zstep.
    replace (wv_nz str 66293) with str by (unfold wv_nz; rewrite (proj2 (Z.eqb_neq str 0) B); reflexivity).
    eapply wv_epi_ps; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR |
                       left; eexists; reflexivity].
  - subst str. do 3 zstep.
    eapply wv_epi_ps; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR |
                       left; eexists; reflexivity].
Qed.

Theorem wv_num_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth str kids keys n : Z)
  (pa pb : list byte),
  mem_inv rsegs m -> wv_node m v 3 str kids keys n pa pb -> 0 < v -> v mod 8 = 0 -> 0 <= str < 2^64 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
                       (junk j16 : list byte),
       ms' = MS (mkR (Z_to_bv 64 WV_R_STRLEN) (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0' t1' t2'
                     (Z_to_bv 64 o) (Z_to_bv 64 (wv_nz str WV_S_ZERO)) (Z_to_bv 64 (wv_nz str WV_S_ZERO))
                     a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 pretty) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 WV_STRLEN) fc None m' (seg_rom rsegs) /\
       wv_inside sp lo m m' junk (Z_to_bv 64 depth) (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 /\
       wv_node m' v 3 str kids keys n pa pb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth str kids keys n pa pb MI ND HV HA HS ST LO DV.
  unfold wv_node, wv_inside, wv_frame in *. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  carve_frame 128%nat ST.
  uwv_pro.
  rewrite wv_sx32 by lia.
  do 2 zstep. if_false.
  do 10 zstep.
  if_cases B; zify_cond B.
  - do 2 zstep.
    replace (wv_nz str 66424) with str by (unfold wv_nz; rewrite (proj2 (Z.eqb_neq str 0) B); reflexivity).
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|exact FR]]]]|exact ND].
  - subst str. do 4 zstep.
    apply evt_done. do 17 eexists. split; [reflexivity|].
    split; [split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|exact FR]]]]|exact ND].
Qed.

Theorem wv_open_call : forall (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo o v pretty depth ty str kids keys n : Z)
  (pa pb : list byte),
  mem_inv rsegs m -> wv_node m v ty str kids keys n pa pb -> (ty = 5 \/ ty = 6) -> 0 < v -> v mod 8 = 0 ->
  stk rsegs m lo (bv_unsigned sp) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs
    (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte)
                       (junk j16 : list byte),
       ms' = MS (mkR (Z_to_bv 64 WV_R_OPEN) (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0' t1' t2'
                     (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 o) (Z_to_bv 64 (wv_open ty)) (Z_to_bv 64 1)
                     a3' a4' a5' a6' a7' s2 (Z_to_bv 64 pretty) s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (Z_to_bv 64 WV_PUT) fc None m' (seg_rom rsegs) /\
       wv_inside sp lo m m' junk (Z_to_bv 64 depth) (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 /\
       wv_node m' v ty str kids keys n pa pb)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 o) (Z_to_bv 64 v) (Z_to_bv 64 pretty) (Z_to_bv 64 depth)
           a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 WRITE_VALUE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    lo o v pretty depth ty str kids keys n pa pb MI ND HT HV HA ST LO DV.
  unfold wv_node, wv_inside, wv_frame in *. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  carve_frame 128%nat ST.
  destruct HT as [-> | ->].
  - uwv_pro.
    rewrite wv_sx32 by lia.
    do 2 zstep. if_false.
    do 10 zstep. if_false.
    do 6 zstep.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|exact FR]]]]|exact ND].
  - uwv_pro.
    rewrite wv_sx32 by lia.
    do 2 zstep. if_false.
    do 10 zstep. if_true.
    do 5 zstep.
    apply evt_done. do 15 eexists. split; [reflexivity|].
    split; [split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|exact FR]]]]|exact ND].
Qed.

Theorem wv_num_tail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (ra1 t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word)
  (m : word -> option byte) (lo : Z) (junk : list byte) (d : word) (c16 : cell),
  mem_inv rsegs m -> wv_frame m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  ((exists j, c16 = CB 8 j) \/ (exists w, c16 = C8 w)) ->
  stk rsegs m lo (bv_unsigned sp - WV_FRAME) -> lo + WV_FRAME <= bv_unsigned sp ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun y0 y1 y2 => y0 = x8 /\ y1 = x9 /\ y2 = x10))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7
           g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6) F (Z_to_bv 64 WV_R_STRLEN) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra1 t0 t1 t2 x8 x9 x10 a1 a2 a3 a4 a5 a6 a7
    g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 m lo junk d c16 MI FR C16 ST LO.
  wv_unfold.
  do 4 zstep.
  eapply wv_epi_put; [apply munch_refl | apply wmono_refl | exact MI | unfold WV_FRAME; lia | exact ST | exact FR |
                      exact C16].
Qed.

Theorem wv_close_tail : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
  (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word)
  (m0 m : word -> option byte) (lo o v ty str kids keys n : Z) (pa pb junk : list byte) (d : word) (c16 : cell),
  munch [(bv_unsigned sp - WV_FRAME, bv_unsigned sp)] m0 m -> wmono rsegs m0 m -> mem_inv rsegs m ->
  wv_node m v ty str kids keys n pa pb -> 0 <= ty < 2^31 ->
  wv_frame m sp junk d c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  ((exists j, c16 = CB 8 j) \/ (exists w, c16 = C8 w)) ->
  stk rsegs m lo (bv_unsigned sp - WV_FRAME) -> lo + WV_FRAME <= bv_unsigned sp ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m0
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 (wv_close ty) /\ x2 = Z_to_bv 64 1))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v)
           a0 a1 a2 a3 a4 a5 a6 a7 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6)
        F (Z_to_bv 64 WV_R_CLOSE) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 m0 m lo o v ty str kids keys n pa pb junk d c16
    MU WM MI ND HT FR C16 ST LO.
  unfold wv_node in ND. wv_unfold.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  zstep. rewrite wv_sx32 by lia.
  do 2 zstep.
  if_cases B; zify_cond B.
  - subst ty. do 4 zstep.
    eapply wv_epi_put; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR | exact C16].
  - do 5 zstep.
    unfold wv_close. wv_unfold. decide_tests.
    eapply wv_epi_put; [exact MU | exact WM | exact MI | unfold WV_FRAME; lia | exact ST | exact FR | exact C16].
Qed.

Theorem wv_after_open_empty : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word)
  (m : word -> option byte) (lo o v pretty ty str kids keys : Z) (pa pb junk j16 : list byte) (d : word),
  mem_inv rsegs m -> wv_node m v ty str kids keys 0 pa pb -> 0 <= ty < 2^31 -> 0 <= pretty < 2^64 ->
  wv_frame m sp junk d (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  stk rsegs m lo (bv_unsigned sp - WV_FRAME) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs (wv_exit (Z_to_bv 64 WV_PUT) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m
               (fun x0 x1 x2 => x0 = Z_to_bv 64 o /\ x1 = Z_to_bv 64 (wv_close ty) /\ x2 = Z_to_bv 64 1))
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v)
           a0 a1 a2 a3 a4 a5 a6 a7 g18 (Z_to_bv 64 pretty) g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6)
        F (Z_to_bv 64 WV_R_OPEN) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 m lo o v pretty ty str kids keys pa pb junk j16 d
    MI ND HT HP FR ST LO DV.
  unfold wv_node in ND. unfold wv_frame in FR. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  pose proof ST as (Hlo & _ & _).
  zstep. if_cases B; zify_cond B.
  - subst pretty. do 2 zstep.
    do 3 zstep. if_true.
    eapply wv_close_tail; [exact MU | exact WM | exact MI | exact ND | exact HT | exact FR |
                           right; eexists; reflexivity | exact ST | exact LO].
  - do 3 zstep.
    do 3 zstep. if_true.
    eapply wv_close_tail; [exact MU | exact WM | exact MI | exact ND | exact HT | exact FR |
                           right; eexists; reflexivity | exact ST | exact LO].
Qed.

Theorem wv_after_open_first : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
  (fc : bv 32) (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 : word)
  (m : word -> option byte) (lo o v pretty depth ty str kids keys n : Z) (pa pb junk j16 : list byte),
  mem_inv rsegs m -> wv_node m v ty str kids keys n pa pb -> 0 < n < 2^64 -> 0 <= pretty < 2^64 ->
  0 <= depth -> depth + 1 < 2^31 ->
  wv_frame m sp junk (Z_to_bv 64 depth) (CB 8 j16) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  stk rsegs m lo (bv_unsigned sp - WV_FRAME) -> lo + WV_FRAME <= bv_unsigned sp ->
  (v + 56 <= bv_unsigned sp - WV_FRAME \/ bv_unsigned sp <= v) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = wv_ls WV_INDENT (Z_to_bv 64 WV_R_INDENT) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 pretty)
              (Z_to_bv 64 (depth + 1)) a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth 0 m' /\
      wv_inside sp lo m m' junk (Z_to_bv 64 depth) (C8 (Z_to_bv 64 (wv_sep pretty))) ra s0 s1 s2 s3 s4 s5 s6 s7
        s8 s9 s10 s11 /\
      wv_node m' v ty str kids keys n pa pb)
    (MS (mkR ra1 (Z_to_bv 64 (bv_unsigned sp - WV_FRAME)) gp tp t0 t1 t2 (Z_to_bv 64 o) (Z_to_bv 64 v)
           a0 a1 a2 a3 a4 a5 a6 a7 g18 (Z_to_bv 64 pretty) g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6)
        F (Z_to_bv 64 WV_R_OPEN) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
    g18 g20 g21 g22 g23 g24 g25 g26 g27 t3 t4 t5 t6 m lo o v pretty depth ty str kids keys n pa pb junk j16
    MI ND HN HP HD HD1 FR ST LO DV.
  unfold wv_node, wv_inside, wv_frame, wv_ls in *. wv_unfold.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  pose proof ST as (Hlo & _ & _).
  zstep. if_cases B; zify_cond B.
  - subst pretty. do 2 zstep.
    do 3 zstep. if_cases B0; zify_cond B0; [exfalso; lia|].
    do 5 zstep. rewrite wv_swrap by lia.
    do 5 zstep.
    rewrite wv_lxor_ltb by lia.
    do 3 zstep. if_true.
    decide_tests.
    zstep. if_false.
    do 4 zstep.
    apply evt_done. do 13 eexists. split; [reflexivity|].
    split; [split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|exact FR]]]]|exact ND].
  - do 3 zstep.
    do 3 zstep. if_cases B0; zify_cond B0; [exfalso; lia|].
    do 5 zstep. rewrite wv_swrap by lia.
    do 5 zstep.
    rewrite wv_lxor_ltb by lia.
    do 3 zstep. if_true.
    decide_tests.
    zstep. if_false.
    do 4 zstep.
    unfold wv_sep, wv_seplen. wv_unfold. decide_tests.
    apply evt_done. do 13 eexists. split; [reflexivity|].
    split; [split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|exact FR]]]]|exact ND].
Qed.

Theorem wv_after_comma : forall (sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word)
  (fc : bv 32) (m : word -> option byte) (o v pretty depth i : Z),
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = wv_ls WV_INDENT (Z_to_bv 64 WV_R_INDENT) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 pretty)
              (Z_to_bv 64 (depth + 1)) a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth i m)
    (wv_ls WV_R_COMMA ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc o v pretty depth i m).
Proof.
  intros. unfold wv_ls. wv_unfold.
  zstep. if_false.
  do 4 zstep.
  apply evt_done. do 12 eexists. reflexivity.
Qed.

Theorem wv_after_sep : forall (sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word)
  (fc : bv 32) (m : word -> option byte) (o v pretty depth i ty str kids keys n : Z) (pa pb : list byte),
  wv_node m v ty str kids keys n pa pb -> 0 < kids -> kids + 56 * n <= 2^64 -> 0 <= i < n -> 56 * n < 2^63 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = wv_ls WRITE_VALUE (Z_to_bv 64 WV_R_ITEM) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (kids + 56 * i))
              (Z_to_bv 64 pretty) (Z_to_bv 64 (depth + 1)) a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth i m)
    (wv_ls WV_R_SEP ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc o v pretty depth i m).
Proof.
  intros sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m o v pretty depth i ty str kids keys n pa pb
    ND HK HKN HI HN.
  unfold wv_node in ND. unfold wv_ls. wv_unfold.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  zstep.
  zstep. rewrite (Z.shiftl_mul_pow2 i 3) by lia.
  zstep. rewrite (Z.shiftl_mul_pow2 i 6) by lia.
  do 4 zstep.
  zstep.
  decide_tests. if_false.
  zstep. if_cases B1; zify_cond B1; [exfalso; lia|].
  zstep. rewrite wv_signed by lia.
  match goal with |- context [Z.shiftr ?x 64] => rewrite (wv_shr x 64) by lia end.
  zstep. rewrite wv_signed by lia.
  match goal with |- context [Z.shiftr ?x 63] => rewrite (wv_shr x 63) by lia end.
  do 3 zstep.
  if_false.
  do 5 zstep.
  apply evt_done. do 11 eexists. reflexivity.
Qed.

Theorem wv_after_indent_arr : forall (sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o v pretty depth i ty str kids keys n : Z)
  (pa pb : list byte),
  wv_node m v ty str kids keys n pa pb -> 0 <= ty < 2^31 -> ty <> 6 -> 0 < kids -> kids + 56 * n <= 2^64 ->
  0 <= i < n -> 56 * n < 2^63 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = wv_ls WRITE_VALUE (Z_to_bv 64 WV_R_ITEM) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (kids + 56 * i))
              (Z_to_bv 64 pretty) (Z_to_bv 64 (depth + 1)) a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth i m)
    (wv_ls WV_R_INDENT ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc o v pretty depth i m).
Proof.
  intros sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m o v pretty depth i ty str kids keys n pa pb
    ND HT H6 HK HKN HI HN.
  pose proof ND as ND0.
  unfold wv_node in ND. unfold wv_ls at 2. wv_unfold.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  zstep. rewrite wv_sx32 by lia.
  zstep. if_cases B; zify_cond B; [|exfalso; lia].
  eapply wv_after_sep; [exact ND0 | exact HK | exact HKN | exact HI | exact HN].
Qed.

Theorem wv_after_indent_obj : forall (sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o v pretty depth i str kids keys n key : Z)
  (pa pb : list byte),
  wv_node m v 6 str kids keys n pa pb -> 0 < keys -> keys mod 8 = 0 -> 0 <= i < n -> 56 * n < 2^63 ->
  bytes_at rsegs m (keys + 8 * i) (le8 (Z_to_bv 64 key)) ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = wv_ls WV_PUT_STRING (Z_to_bv 64 WV_R_KEY) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 key)
              a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth i m)
    (wv_ls WV_R_INDENT ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc o v pretty depth i m).
Proof.
  intros sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m o v pretty depth i str kids keys n key pa pb
    ND HK HA HI HN KB.
  unfold wv_node in ND. unfold wv_ls. wv_unfold.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  pose proof (bytes_at_bound _ _ _ _ KB) as RK. rewrite length_le8 in RK.
  assert (RD : ov_read_bytes rsegs m (wa (keys + 8 * i)) 8 = Some (le8 (Z_to_bv 64 key))).
  { replace (wa (keys + 8 * i)) with (wa (keys + 8 * i + 0)) by (f_equal; lia).
    rewrite (bytes_at_read rsegs m _ _ 0 8 KB ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  zstep. rewrite wv_sx32 by lia.
  zstep. if_false.
  do 5 zstep.
  decide_tests. if_false.
  zstep.
  match goal with |- context [Z.shiftr ?x 60] => rewrite (wv_shr x 60) by lia end.
  zstep. if_false.
  zstep. if_cases B1; zify_cond B1; [exfalso; lia|].
  zstep. if_cases B2; zify_cond B2; [exfalso; lia|].
  do 2 zstep.
  match goal with |- context [Z.land ?x 7] => rewrite (wv_land7 x) by (Z.div_mod_to_equations; lia) end.
  zstep. if_false.
  do 3 zstep.
  apply evt_done. do 13 eexists. reflexivity.
Qed.

Theorem wv_after_key : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word)
  (fc : bv 32) (m : word -> option byte) (o v pretty depth i : Z) (junk : list byte) (d : word),
  wv_frame m sp junk d (C8 (Z_to_bv 64 (wv_sep pretty))) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = wv_ls WV_PUT (Z_to_bv 64 WV_R_SEP) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 (wv_sep pretty))
              (Z_to_bv 64 (wv_seplen pretty)) a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth i m)
    (wv_ls WV_R_KEY ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc o v pretty depth i m).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m
    o v pretty depth i junk d FR.
  unfold wv_frame, wv_ls in *. wv_unfold.
  do 4 zstep.
  apply evt_done. do 12 eexists. reflexivity.
Qed.

Theorem wv_after_item_next : forall (sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o v pretty depth i ty str kids keys n : Z)
  (pa pb : list byte),
  wv_node m v ty str kids keys n pa pb -> 0 <= i -> i + 1 < n -> 56 * n < 2^63 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = wv_ls WV_PUT (Z_to_bv 64 WV_R_COMMA) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 WV_S_COMMA)
              (Z_to_bv 64 1) a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth (i + 1) m)
    (wv_ls WV_R_ITEM ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc o v pretty depth i m).
Proof.
  intros sp gp tp ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m o v pretty depth i ty str kids keys n pa pb
    ND HI HI1 HN.
  unfold wv_node in ND. unfold wv_ls. wv_unfold.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  do 5 zstep.
  if_cases B; zify_cond B; [|exfalso; lia].
  zstep. if_cases B1; zify_cond B1; [exfalso; lia|].
  do 4 zstep.
  replace (56 * i + 56) with (56 * (i + 1)) by ring.
  replace (8 * i + 8) with (8 * (i + 1)) by ring.
  apply evt_done. do 12 eexists. reflexivity.
Qed.

Theorem wv_after_item_last : forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
  (ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
  (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o v pretty depth i ty str kids keys n : Z)
  (pa pb junk : list byte) (c16 : cell),
  wv_node m v ty str kids keys n pa pb -> 0 <= i -> i + 1 = n -> 56 * n < 2^63 ->
  wv_frame m sp junk (Z_to_bv 64 depth) c16 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      ms' = wv_ls WV_INDENT (Z_to_bv 64 WV_R_CLOSE) sp gp tp t0' t1' t2' (Z_to_bv 64 o) (Z_to_bv 64 pretty)
              (Z_to_bv 64 depth) a3' a4' a5' a6' a7' t3' t4' t5' t6' F fc o v pretty depth (i + 1) m)
    (wv_ls WV_R_ITEM ra1 sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc o v pretty depth i m).
Proof.
  intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
    F fc m o v pretty depth i ty str kids keys n pa pb junk c16 ND HI HI1 HN FR.
  unfold wv_node, wv_frame, wv_ls in *. wv_unfold.
  pose proof (rw_cells_bound _ _ _ _ ND) as RV. cbn [cells_size csize Nat.add] in RV.
  do 5 zstep.
  if_cases B; zify_cond B; [exfalso; lia|].
  zstep. if_cases B1; zify_cond B1; [exfalso; lia|].
  do 4 zstep.
  replace (56 * i + 56) with (56 * (i + 1)) by ring.
  replace (8 * i + 8) with (8 * (i + 1)) by ring.
  apply evt_done. do 12 eexists. reflexivity.
Qed.

Lemma wv_img_null : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_NULL (map (Z_to_bv 8) [110; 117; 108; 108]).
Proof.
  intros m MI. unfold WV_S_NULL.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_false : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_FALSE (map (Z_to_bv 8) [102; 97; 108; 115; 101]).
Proof.
  intros m MI. unfold WV_S_FALSE.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_true : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_TRUE (map (Z_to_bv 8) [116; 114; 117; 101]).
Proof.
  intros m MI. unfold WV_S_TRUE.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_zero : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_ZERO (map (Z_to_bv 8) [48; 0]).
Proof.
  intros m MI. unfold WV_S_ZERO.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_empty : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_EMPTY (map (Z_to_bv 8) [0]).
Proof.
  intros m MI. unfold WV_S_EMPTY.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_lbracket : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_LBRACKET (map (Z_to_bv 8) [91]).
Proof.
  intros m MI. unfold WV_S_LBRACKET.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_lbrace : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_LBRACE (map (Z_to_bv 8) [123]).
Proof.
  intros m MI. unfold WV_S_LBRACE.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_rbracket : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_RBRACKET (map (Z_to_bv 8) [93]).
Proof.
  intros m MI. unfold WV_S_RBRACKET.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_rbrace : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_RBRACE (map (Z_to_bv 8) [125]).
Proof.
  intros m MI. unfold WV_S_RBRACE.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_comma : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_COMMA (map (Z_to_bv 8) [44]).
Proof.
  intros m MI. unfold WV_S_COMMA.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_colon : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_COLON (map (Z_to_bv 8) [58]).
Proof.
  intros m MI. unfold WV_S_COLON.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.

Lemma wv_img_colon_sp : forall m, mem_inv rsegs m -> bytes_at rsegs m WV_S_COLON_SP (map (Z_to_bv 8) [58; 32]).
Proof.
  intros m MI. unfold WV_S_COLON_SP.
  apply ro_bytes_at; [exact MI | lia | rewrite length_map; cbn [length]; lia |].
  apply ro_bytes_b_sound. vm_compute. reflexivity.
Qed.
