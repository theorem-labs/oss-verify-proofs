(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_ikit Z_infl_defs Z_infl_defs2 Z_infl_c_pure Z_infl_c_tab Zg_infl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZProg ZIface InflateState InflateArms Inflate InflateFast InffastModel InffastCtx InffastSafe InffastMem RefInffast17 RefInffast_run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zext32_land : forall v, Z.land (Z.land v 18446744073709551615) 4294967295 = wrap32 v.
Proof.
  intros v. unfold wrap32. rewrite <- Z.land_assoc. f_equal.
Qed.
(* [comment removed for export] *)
Lemma zext32_swrap : forall v, Z.land (Z.land (bv_swrap 32 v) 18446744073709551615) 4294967295 = wrap32 v.
Proof.
  intros v. rewrite zext32_land. rewrite !wrap32_mod. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul]. change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.
Lemma wrap32_swrap : forall v, wrap32 (bv_swrap 32 v) = wrap32 v.
Proof. intros v. rewrite <- (zext32_swrap v). symmetry. apply zext32_land. Qed.
(* [comment removed for export] *)
Lemma wrap32_modl : forall z, wrap32 z = z mod 4294967296.
Proof. intros z. rewrite wrap32_mod. reflexivity. Qed.
Lemma wrap64_modl : forall z, wrap64 z = z mod 18446744073709551616.
Proof. intros z. unfold wrap64. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. reflexivity. Qed.
(* [comment removed for export] *)
Lemma zmask_ones : forall n, 0 <= n <= 31 -> zmask n = Z.ones n.
Proof. intros n Hn. rewrite zmask_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_FF_LOOP : Z := 0x1fa20.    (* [comment removed for export] *)
Definition PC_FF_DOLEN : Z := 0x1fa68.   (* [comment removed for export] *)
Definition PC_FF_LIT : Z := 0x1fab0.     (* [comment removed for export] *)
Definition PC_FF_COND : Z := 0x1fac0.    (* [comment removed for export] *)
Definition PC_FF_LEN : Z := 0x1facc.     (* [comment removed for export] *)
Definition PC_FF_DLOOK : Z := 0x1fb08.   (* [comment removed for export] *)
Definition PC_FF_DODIST : Z := 0x1fb54.  (* [comment removed for export] *)
Definition PC_FF_DIST : Z := 0x1fb94.    (* [comment removed for export] *)
Definition PC_FF_WIN : Z := 0x1fbf8.     (* [comment removed for export] *)
Definition PC_FF_OUT : Z := 0x1fc78.     (* [comment removed for export] *)
Definition PC_FF_W3A : Z := 0x1fd48.     (* [comment removed for export] *)
Definition PC_FF_W3B : Z := 0x1fd4c.     (* [comment removed for export] *)
Definition PC_FF_W3 : Z := 0x1fd50.      (* [comment removed for export] *)
Definition PC_FF_BRK1 : Z := 0x1fdd0.    (* [comment removed for export] *)
Definition PC_FF_BRK2 : Z := 0x1fdf0.    (* [comment removed for export] *)
Definition PC_FF_BRK3 : Z := 0x1fe88.    (* [comment removed for export] *)
Definition PC_FF_EXIT : Z := 0x1fe08.    (* [comment removed for export] *)
Definition FF_FRAME : Z := 112.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record ffsave : Type := mkFS {
  fs_ra : word; fs_x8 : word; fs_x9 : word; fs_x18 : word; fs_x19 : word; fs_x20 : word; fs_x21 : word;
  fs_x22 : word; fs_x23 : word; fs_x24 : word; fs_x25 : word; fs_x26 : word; fs_x27 : word }.

Definition ff_frame_cells (s : inflate_state) (sv : ffsave) : list cell :=
  [C8 (wz (is_wnext s + is_wsize s)); C8 (fs_x27 sv); C8 (fs_x26 sv); C8 (fs_x25 sv); C8 (fs_x24 sv); C8 (fs_x23 sv); C8 (fs_x22 sv);
   C8 (fs_x21 sv); C8 (fs_x20 sv); C8 (fs_x19 sv); C8 (fs_x18 sv); C8 (fs_x9 sv); C8 (fs_x8 sv); C8 (fs_ra sv)].

(* [comment removed for export] *)
Definition ff_sp (X : ictx) : Z := bv_unsigned (ix_sp X) + -336.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section States.
Variables (X : ictx) (s : inflate_state) (c : icall) (r : iregs).
Let L := ix_L X.
Let xx := ffx_of s c r.

(* [comment removed for export] *)
Definition FFL (f : ffs) (pc : Z) (x1 x7 x21 x25 x26 x27 : word) (m : mem) : machine_state :=
  MS (mkR x1 (wz (ff_sp X)) (ix_gp X) (ix_tp X) (wz (-1)) (wz 14) x7
          (wz (win_addr L (is_window_blk s))) (wz (cp_addr L (is_lencode s))) (wz (il_S L))
          (wz (f_hold f)) (wz (il_As L)) (wz (il_NI L + f_in f)) (wz (il_NO L + f_out f))
          (wz (il_NI L + x_last xx)) (wz (il_NO L + x_end xx)) (wz (f_bits f))
          (wz (cp_addr L (is_distcode s))) (wz (il_As L + 7160)) (wz (il_NO L + x_beg xx)) x21
          (wz (x_lmask xx)) (wz (x_dmask xx)) (wz (win_addr L (is_window_blk s) + wrap32 (is_wnext s - 1) + 1))
          x25 x26 x27 (wz 2) (wz (is_wsize s)) (wz (is_whave s)) (wz (is_wnext s)))
     (ix_F X) (wz pc) (ix_fc X) None m (seg_rom psegs).

(* [comment removed for export] *)
Definition FFX (f : ffs) (x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (m : mem) : machine_state :=
  MS (mkR x1 (wz (ff_sp X)) (ix_gp X) (ix_tp X) x5 (wz 14) x7 x8 x9 (wz (il_S L))
          (wz (f_hold f)) (wz (il_As L)) (wz (il_NI L + f_in f)) (wz (il_NO L + f_out f))
          (wz (il_NI L + x_last xx)) (wz (il_NO L + x_end xx)) (wz (f_bits f))
          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
     (ix_F X) (wz PC_FF_EXIT) (ix_fc X) None m (seg_rom psegs).

(* [comment removed for export] *)
Lemma FFL_intro : forall f pc x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (ff_sp X) -> x3 = ix_gp X -> x4 = ix_tp X -> x5 = wz (-1) -> x6 = wz 14 ->
  x8 = wz (win_addr L (is_window_blk s)) -> x9 = wz (cp_addr L (is_lencode s)) -> x10 = wz (il_S L) ->
  x11 = wz (f_hold f) -> x12 = wz (il_As L) -> x13 = wz (il_NI L + f_in f) -> x14 = wz (il_NO L + f_out f) ->
  x15 = wz (il_NI L + x_last xx) -> x16 = wz (il_NO L + x_end xx) -> x17 = wz (f_bits f) ->
  x18 = wz (cp_addr L (is_distcode s)) -> x19 = wz (il_As L + 7160) -> x20 = wz (il_NO L + x_beg xx) ->
  x22 = wz (x_lmask xx) -> x23 = wz (x_dmask xx) -> x24 = wz (win_addr L (is_window_blk s) + wrap32 (is_wnext s - 1) + 1) ->
  x28 = wz 2 -> x29 = wz (is_wsize s) -> x30 = wz (is_whave s) -> x31 = wz (is_wnext s) -> F = ix_F X -> fc = ix_fc X ->
  MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz pc) fc None m (seg_rom psegs)
  = FFL f pc x1 x7 x21 x25 x26 x27 m.
Proof. intros. subst. reflexivity. Qed.

(* [comment removed for export] *)
Lemma FFL_intro2 : forall f pc y1 y7 y21 y25 y26 y27 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x1 = y1 -> x7 = y7 -> x21 = y21 -> x25 = y25 -> x26 = y26 -> x27 = y27 ->
  x2 = wz (ff_sp X) -> x3 = ix_gp X -> x4 = ix_tp X -> x5 = wz (-1) -> x6 = wz 14 ->
  x8 = wz (win_addr L (is_window_blk s)) -> x9 = wz (cp_addr L (is_lencode s)) -> x10 = wz (il_S L) ->
  x11 = wz (f_hold f) -> x12 = wz (il_As L) -> x13 = wz (il_NI L + f_in f) -> x14 = wz (il_NO L + f_out f) ->
  x15 = wz (il_NI L + x_last xx) -> x16 = wz (il_NO L + x_end xx) -> x17 = wz (f_bits f) ->
  x18 = wz (cp_addr L (is_distcode s)) -> x19 = wz (il_As L + 7160) -> x20 = wz (il_NO L + x_beg xx) ->
  x22 = wz (x_lmask xx) -> x23 = wz (x_dmask xx) -> x24 = wz (win_addr L (is_window_blk s) + wrap32 (is_wnext s - 1) + 1) ->
  x28 = wz 2 -> x29 = wz (is_wsize s) -> x30 = wz (is_whave s) -> x31 = wz (is_wnext s) -> F = ix_F X -> fc = ix_fc X ->
  MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz pc) fc None m (seg_rom psegs)
  = FFL f pc y1 y7 y21 y25 y26 y27 m.
Proof. intros. subst. reflexivity. Qed.

Lemma FFX_intro : forall f x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 F fc m,
  x2 = wz (ff_sp X) -> x3 = ix_gp X -> x4 = ix_tp X -> x6 = wz 14 -> x10 = wz (il_S L) ->
  x11 = wz (f_hold f) -> x12 = wz (il_As L) -> x13 = wz (il_NI L + f_in f) -> x14 = wz (il_NO L + f_out f) ->
  x15 = wz (il_NI L + x_last xx) -> x16 = wz (il_NO L + x_end xx) -> x17 = wz (f_bits f) -> F = ix_F X -> fc = ix_fc X ->
  MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) F (wz PC_FF_EXIT) fc None m (seg_rom psegs)
  = FFX f x1 x5 x7 x8 x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 m.
Proof. intros. subst. reflexivity. Qed.
End States.

(* [comment removed for export] *)
Ltac ffreg :=
  first [ reflexivity | f_equal; lia
        | f_equal; rewrite ?zext32_swrap, ?zext32_land, ?wrap32_swrap; rewrite ?wrap32_id, ?wrap64_id by lia; lia
        | f_equal; rewrite ?zext32_swrap, ?zext32_land, ?wrap32_swrap, ?wrap32_modl, ?wrap64_modl; Z.div_mod_to_equations; lia
        | apply Z_to_bv_eqm; rewrite ?zext32_swrap, ?zext32_land, ?wrap32_swrap, ?wrap32_modl, ?wrap64_modl, ?Z.mod_mod by lia;
          first [ reflexivity | Z.div_mod_to_equations; lia ] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Mem.
Variables (X : ictx) (s : inflate_state) (c : icall) (sv : ffsave).
Let L := ix_L X.

(* [comment removed for export] *)
Definition FFMg (s1 : inflate_state) (c1 : icall) (f : ffs) (m : mem) : Prop :=
  rw_cells psegs m (ff_sp X) (ff_frame_cells s sv)
  /\ isA m L s1 /\ isT m L s /\ izs m L c1
  /\ icodes m L s /\ iwin m L s /\ iin m X
  /\ iout m L (ix_rest0 X) (icset_outbuf c (f_ob f)) (f_out f)
  /\ mem_inv psegs m
  /\ iarrs s /\ ilay_ok L s.
Definition FFM := FFMg s c.
End Mem.

(* [comment removed for export] *)
Definition ffW (X : ictx) : list ivl := [(il_NO (ix_L X), il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X)))].
(* [comment removed for export] *)
Definition ffWb (X : ictx) : list ivl :=
  [(il_NO (ix_L X), il_NO (ix_L X) + Z.of_nat (length (ix_rest0 X))); (il_S (ix_L X), il_S (ix_L X) + 112);
   (il_As (ix_L X), il_As (ix_L X) + 168)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FINV (X : ictx) (s : inflate_state) (c : icall) (f : ffs) : Prop :=
  0 <= f_bits f <= 63 /\ 0 <= f_hold f < 2 ^ f_bits f
  /\ ic_next_in c <= f_in f <= arr_len (ic_input c)
  /\ ic_next_out c <= f_out f <= arr_len (ic_outbuf c)
  /\ arr_len (f_ob f) = arr_len (ic_outbuf c)
  /\ (forall i, 0 <= i < f_out f -> 0 <= arr_get (f_ob f) i < 256).

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pure.
Variables (x : ffx) (s : inflate_state) (IN ON WN : Z).

Definition ff_stepf (f : ffs) : ffs + (ffs * option (Z * option Z)) :=
  match fast_trip x s f with
  | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then inl f' else inr (f', None)
  | FBreak f' mode msg => inr (f', Some (mode, msg))
  end.
(* [comment removed for export] *)
Definition ffL (n : Z) (f : ffs) : ffs * option (Z * option Z) := iterZ n ff_stepf (fun f => (f, None)) f.

Lemma ffL_step : forall n f, 0 < n ->
  ffL n f = match fast_trip x s f with
            | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then ffL (n - 1) f' else (f', None)
            | FBreak f' mode msg => (f', Some (mode, msg))
            end.
Proof.
  intros n f Hn. unfold ffL at 1. rewrite iterZ_step by exact Hn. unfold ff_stepf at 1.
  destruct (fast_trip x s f) as [f'|f' md g]; [|reflexivity]. destruct (_ && _); reflexivity.
Qed.

Lemma loop_ok_step : forall n f, 0 < n ->
  loop_ok x s IN ON WN n f =
    if trip_ok x s IN ON WN f then
      match fast_trip x s f with
      | FCont f' => if (f_in f' <? x_last x) && (f_out f' <? x_end x) then loop_ok x s IN ON WN (n - 1) f' else exit_ok f'
      | FBreak f' _ _ => exit_ok f'
      end
    else false.
Proof.
  intros n f Hn. unfold loop_ok at 1. rewrite iterZ_step by exact Hn.
  destruct (trip_ok x s IN ON WN f); [|reflexivity].
  destruct (fast_trip x s f) as [f'|f' md g]; [|reflexivity]. destruct (_ && _); reflexivity.
Qed.
Lemma loop_ok_le0 : forall n f, n <= 0 -> loop_ok x s IN ON WN n f = false.
Proof. intros n f Hn. unfold loop_ok. rewrite iterZ_le0 by exact Hn. reflexivity. Qed.
End Pure.

Lemma ff_loop_ffL : forall s c r, ff_loop s c r = ffL (ffx_of s c r) s (8 * ic_avail_in c + ic_avail_out c + 80) (ff0_of s c).
Proof. intros. reflexivity. Qed.
Lemma ff_ok_loop_ok : forall s c r, ff_ok s c r = loop_ok (ffx_of s c r) s (arr_len (ic_input c)) (arr_len (ic_outbuf c)) (arr_len (is_window s))
                                                       (8 * ic_avail_in c + ic_avail_out c + 80) (ff0_of s c).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ffx_facts : forall X s c r, ff_restored s c r -> ff_typed X s c r ->
  ic_next_in c <= x_last (ffx_of s c r) < ic_next_in c + 4294967296
  /\ ic_next_out c <= x_end (ffx_of s c r) < ic_next_out c + 4294967296
  /\ 0 <= x_beg (ffx_of s c r) <= ic_next_out c
  /\ 0 <= x_lmask (ffx_of s c r) < 4294967296 /\ 0 <= x_dmask (ffx_of s c r) < 4294967296
  /\ x_last (ffx_of s c r) = ic_next_in c + wrap32 (ic_avail_in c - 5)
  /\ x_end (ffx_of s c r) = ic_next_out c + wrap32 (ic_avail_out c - 257)
  /\ x_beg (ffx_of s c r) = ic_next_out c - wrap32 (ir_out r - ic_avail_out c).
Proof.
  intros X s c r (E1 & E2 & E3 & E4 & E5 & E6) HT.
  destruct HT as (Pin & Pout & Rn & Rh & Rnh & Rin31 & Rp & Rl & Rpl & Rout31 & Rout & Rbeg & Bin & Bout & Bwin & Rb & Rhold
               & Rlb & Rdb & CPL & CPD & Rws & Rwh & Rwn & Rsane & Wnone & Wz & Whas).
  rewrite <- E1, <- E2, <- E3, <- E4 in *.
  unfold ffx_of. cbn [x_last x_end x_beg x_lmask x_dmask].
  pose proof (wrap32_range (ic_avail_in c - 5)). pose proof (wrap32_range (ic_avail_out c - 257)). pose proof (wrap32_range (ir_out r - ic_avail_out c)).
  unfold zmask. pose proof (wrap32_range (Z.shiftl 1 (is_lenbits s) - 1)). pose proof (wrap32_range (Z.shiftl 1 (is_distbits s) - 1)).
  change (2^32) with 4294967296 in *. repeat split; lia.
Qed.

Ltac ffx_pose HRS HT :=
  let a := fresh "RLAST" in let b := fresh "REND" in let c := fresh "RBEG" in let d := fresh "RLM" in let e := fresh "RDM" in
  let f := fresh "ELAST" in let g := fresh "EEND" in let h := fresh "EBEG" in
  destruct (ffx_facts _ _ _ _ HRS HT) as (a & b & c & d & e & f & g & h).

(* [comment removed for export] *)
Lemma srliw3_small : forall b, 0 <= b < 2147483648 -> bv_swrap 32 (bv_wrap 32 b ≫ 3) = b / 8.
Proof.
  intros b Hb. rewrite (bv_wrap_small 32 b) by (unfold bv_modulus; cbn; lia). rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  apply bv_swrap32_id. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma le4_swrap32_add : forall a k, le4 (wz (bv_swrap 32 a + k)) = le4 (wz (wrap32 (a + k))).
Proof.
  intros a k. apply le4_wz_mod. rewrite Z_to_bv_unsigned. rewrite wrap32_mod.
  unfold bv_wrap, bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. cbn [Z.of_N Z.pow Z.pow_pos Pos.iter Z.mul Pos.mul].
  change (4294967296 / 2) with 2147483648. change (2^32) with 4294967296. Z.div_mod_to_equations. lia.
Qed.
