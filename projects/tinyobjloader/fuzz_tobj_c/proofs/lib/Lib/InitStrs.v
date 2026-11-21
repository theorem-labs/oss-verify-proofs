(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the entry-stack layout of the new model: the strings tail after the pad, the random bytes inside the head, the auxv size by CONFIG_RSEQ; the launch conjunct in place of the entry-stack fit; written as plain text; the section's local definitions cleared before each arithmetic step of a lemma that does not take them; Jinit_set_rw and recarve_strs write a variable at 14 or above, as the launch's Jinit now also fixes variable 13, AT_EXECFN's address). *)

From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymObj SymCall Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import InitLayout InitState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

(* The strings object a driver carves from the launch image: base [SVar 4] (argv[0]'s address, i.e.
   [sp + str_off]), extent [SVar nv], bytes the list variable [nl]. *)
Definition O_strs (nv nl : positive) : sobj :=
  mkObj (SVar 4) (SLit 0) (SVar nv) [] (DList nl).

(* LPS 727298f3: the launch image is Lib/InitLayout.v's [bsb_decomp]: the head (argc, argv, envp, auxv,
   the gap and AT_RANDOM's 16 bytes at [rand_off]), the pad, then from [str_off] the strings of argv,
   envp and AT_EXECFN, a zero byte and a zero word.  So the tail from [str_off] no longer holds the
   random bytes (they lie below it, in their own region), and the auxv object is [auxv_size] bytes,
   which depends on CONFIG_RSEQ. *)
Section Strs.
Variable segs : list Segment.
Variable pc0 : N.
Variable ph : PhdrInfo.
Variable data_lo data_hi : Z.
Hypothesis Hdata : data_ok_b segs data_lo data_hi = true.
Hypothesis Hdata_hi : data_hi <= 2 ^ 40.
Hypothesis Htop : segs_top segs <= 2 ^ 40.
Variables sp brk mb : word.
Variable draw : EntryDraw.
Variable lim : Z.
Variable inp : ProcInput.
Hypothesis Hsp : valid_sp sp.
Hypothesis Hinp : valid_input_either inp.
Hypothesis Hlaunch : entry_launch_ok_va Sv48 (mkEntry sp brk mb draw) inp.

Let argv := in_argv inp.
Let envp := in_envp inp.
Let ARGC := Z.of_nat (length argv).
Let ENVC := Z.of_nat (length envp).
Let STR := Z.of_nat (str_off inp sp draw).
Let RND := Z.of_nat (rand_off inp).
Let PAD := Z.of_nat (pad_len inp sp draw).
Let LEN := Z.of_nat (img_len inp sp draw).
Let AUX := Z.of_nat (auxv_size (kb_rseq (in_kernel inp))).
Let argv0 : list byte := nth 0 argv [].
Let ms0 : machine_state := InitState.ms0 segs pc0 ph sp mb draw inp.
Let JI : valuation -> Prop := Jinit segs pc0 ph sp mb draw inp.

Lemma Hsp_hiS : (bv_unsigned sp <= launch_sp_hi (ed_top draw) inp)%Z.
Proof using Hlaunch argv envp ARGC ENVC STR RND PAD LEN AUX argv0. destruct Hlaunch as (_ & (_ & _ & H) & _). exact H. Qed.

Definition strs_tail : list byte :=
  flatten_strings argv ++ flatten_strings envp ++ in_execfn inp ++ [Z_to_bv 8 0] ++ repeat (Z_to_bv 8 0) 8.

Lemma region_tail : region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw (str_off inp sp draw) strs_tail.
Proof using Hlaunch argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  pose proof Hsp_hiS as HH.
  eapply (region_at inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw
            (hdr_bytes inp sp draw ++ env_bytes inp sp draw ++ auxv inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw
             ++ repeat (Z_to_bv 8 0) (8 * (block_items argv envp mod 2))
             ++ rand_bytes draw ++ repeat (Z_to_bv 8 0) (pad_len inp sp draw))
            _ []).
  - rewrite (bsb_decomp inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw HH). unfold strs_tail.
    rewrite <- !app_assoc, app_nil_r. reflexivity.
  - rewrite !length_app, length_hdr_bytes, length_env_bytes, length_auxv, !repeat_length, length_rand_bytes.
    unfold argv, envp, str_off, pad_len, block_head_size, block_items, argc, envc. clear - HH. lia.
Qed.

(* The random bytes are no longer in the tail: they have their own region below [str_off]. *)
Lemma region_rnd : region inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw (rand_off inp) (rand_bytes draw).
Proof using Hlaunch argv envp ARGC ENVC STR RND PAD LEN AUX argv0. exact (region_rand inp mb ph (Z_to_bv 64 (Z.of_N pc0)) sp draw Hsp_hiS). Qed.

Lemma NUMS :
  (140735340871680 <= bv_unsigned sp <= 140737488355328)
  /\ bv_unsigned sp mod 16 = 0
  /\ (1 <= ARGC <= 1024)
  /\ (0 <= ENVC <= 256)
  /\ STR = RND + 16 + PAD
  /\ Z.of_nat (length argv0) + 1 <= Z.of_nat (tab argv)
  /\ Z.of_nat (length argv0) <= 131071
  /\ RND = 8 * ARGC + 8 * ENVC + 24 + AUX + 8 * Z.of_nat (Nat.modulo (block_items argv envp) 2)
  /\ PAD <= 4110
  /\ Z.of_nat (tab argv) <= 2097152
  /\ Z.of_nat (tab envp) <= 131072
  /\ LEN = STR + Z.of_nat (launch_string_bytes argv envp (in_execfn inp)) + 8
  /\ RND mod 8 = 0
  /\ (bv_unsigned sp + LEN) mod 4096 = 0.
Proof using Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0. exact (nums pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch). Qed.

(* Every bound the lemmas below use: [NUMS], the auxv size range, the parity gap, the fit below the
   stack window's top. *)
Lemma BOUNDS :
  432 <= AUX <= 464
  /\ 0 <= Z.of_nat (Nat.modulo (block_items argv envp) 2) <= 1
  /\ bv_unsigned sp + LEN <= 140737488355328
  /\ LEN <= 4194304 - 16.
Proof using Hinp Hlaunch pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  pose proof (auxv_size_le (kb_rseq (in_kernel inp))). pose proof (auxv_size_ge (kb_rseq (in_kernel inp))).
  pose proof (Nat.mod_upper_bound (block_items argv envp) 2 ltac:(lia)).
  pose proof (LEN_fit pc0 ph sp brk mb draw inp Hlaunch) as LF. rewrite sp_hi_val in LF.
  pose proof (LEN_bound pc0 ph sp brk mb draw inp Hinp Hlaunch) as LB.
  unfold AUX, LEN. repeat split; lia.
Qed.

Lemma length_tail : Z.of_nat (length strs_tail) = LEN - STR.
Proof using Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  pose proof NUMS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HL & _).
  unfold strs_tail. rewrite !length_app, repeat_length. cbn [length].
  rewrite HL. unfold launch_string_bytes. lia.
Qed.

Lemma tail_nth_str0 : forall j : nat, (j <= length argv0)%nat ->
  nth j strs_tail (Z_to_bv 8 0) = nth j (argv0 ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof using Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  intros j Hj. unfold strs_tail. pose proof NUMS. subst argv0 ARGC.
  destruct argv as [|a r] eqn:Ea; [cbn in *; lia|].
  rewrite flatten_strings_cons. cbn [nth]. rewrite <- app_assoc. apply app_nth1.
  rewrite length_app. cbn [length]. cbn in Hj. lia.
Qed.

Lemma rand_bytes_nth : forall (k i : nat), (k < 2)%nat -> (i < 8)%nat ->
  nth (8 * k + i) (rand_bytes draw) (Z_to_bv 8 0)
  = nth i (enc_bytes 8 (nth k [rnd0 draw; rnd1 draw] (Z_to_bv 64 0))) (Z_to_bv 8 0).
Proof using .
  intros k i Hk Hi. unfold rand_bytes. rewrite at_random_bytes_words.
  (* [clear - Hk Hi]: a bare [lia] here reads the section's Lets (ARGC, STR, ..) and so makes the proof
     depend on [sp] and [inp], which this [Proof using .] does not declare. *)
  rewrite nth_flat_map_le8 by (cbn; clear - Hk Hi; lia). rewrite word_le8_enc. reflexivity.
Qed.

Section J.
Variable rho : valuation.
Hypothesis HJ : JI rho.

Ltac bounds := pose proof NUMS; pose proof BOUNDS.

Lemma J_v1 : bv_unsigned (eval rho (SVar 1)) = bv_unsigned sp.
Proof using HJ argv envp ARGC ENVC STR RND PAD LEN AUX argv0. cbn [eval]. rewrite (ji_sp _ _ _ _ _ _ _ _ HJ). reflexivity. Qed.
Lemma J_v2 : bv_unsigned (eval rho (SVar 2)) = ARGC.
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0. cbn [eval]. rewrite (ji_argc _ _ _ _ _ _ _ _ HJ). bounds. apply U_addr. lia. Qed.
Lemma J_v3 : bv_unsigned (eval rho (SVar 3)) = ENVC.
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0. cbn [eval]. rewrite (ji_envc _ _ _ _ _ _ _ _ HJ). bounds. apply U_addr. lia. Qed.
Lemma J_v4 : bv_unsigned (eval rho (SVar 4)) = bv_unsigned sp + STR.
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0. cbn [eval]. rewrite (ji_argv0 _ _ _ _ _ _ _ _ HJ). bounds. apply U_addr. lia. Qed.
Lemma J_v5 : bv_unsigned (eval rho (SVar 5)) = Z.of_nat (length argv0).
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0. cbn [eval]. rewrite (ji_len0 _ _ _ _ _ _ _ _ HJ). bounds. apply U_addr. lia. Qed.
Lemma J_v6 : bv_unsigned (eval rho (SVar 6)) = bv_unsigned sp + RND.
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0. cbn [eval]. rewrite (ji_rand _ _ _ _ _ _ _ _ HJ). bounds. apply U_addr. lia. Qed.
Lemma J_lit : forall z : Z, 0 <= z < 2 ^ 64 -> bv_unsigned (eval rho (SLit z)) = z.
Proof using . intros. cbn [eval]. apply U_addr. assumption. Qed.

Lemma J_add : forall (a b : sv) (x y : Z),
  bv_unsigned (eval rho a) = x -> bv_unsigned (eval rho b) = y -> 0 <= x -> 0 <= y -> x + y < 2 ^ 64 ->
  bv_unsigned (eval rho (SAlu ALU_ADD a b)) = x + y.
Proof using .
  (* [clear - ..] before each [lia] here and below in this file's [Proof using .] lemmas: a bare [lia]
     reads the section's Lets (ARGC, STR, ..) and so uses [sp] and [inp], which these lemmas do not
     declare. *)
  intros a b x y Hx Hy H1 H2 H3. cbn [eval]. unfold alu64, alu. rewrite bv_add_unsigned, Hx, Hy.
  unfold bv_wrap. rewrite mod64. apply Z.mod_small. clear - H1 H2 H3. lia.
Qed.

Lemma J_sll3 : forall (i : positive) (x : Z),
  bv_unsigned (eval rho (SVar i)) = x -> 0 <= x < 2 ^ 50 -> bv_unsigned (eval rho (sll3 i)) = 8 * x.
Proof using .
  intros i x Hx Hr. unfold sll3. cbn [eval]. rewrite sll_val. change (3 mod 64) with 3.
  rewrite Z.shiftl_mul_pow2 by (clear - Hr; lia). change (2 ^ 3) with 8.
  cbn [eval] in Hx. rewrite Hx. rewrite Z.mod_small; [clear - Hr; lia|]. rewrite pow64. clear - Hr. lia.
Qed.

Lemma J_env_base : bv_unsigned (eval rho env_base) = bv_unsigned sp + 8 * ARGC + 16.
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  bounds. unfold env_base.
  erewrite J_add; [reflexivity| | apply J_lit; lia | | |lia]; try lia.
  erewrite J_add; [reflexivity| apply J_v1 | apply (J_sll3 2 ARGC J_v2); lia | | |]; lia.
Qed.

Lemma J_aux_base : bv_unsigned (eval rho aux_base) = bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24.
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  bounds. unfold aux_base.
  erewrite J_add; [reflexivity| | apply J_lit; lia | | |lia]; try lia.
  erewrite J_add; [reflexivity| | apply (J_sll3 3 ENVC J_v3); lia | | |]; try lia.
  erewrite J_add; [reflexivity| apply J_v1 | apply (J_sll3 2 ARGC J_v2); lia | | |]; lia.
Qed.

Lemma J_soff_small : forall (e : sv) (x : Z), bv_unsigned (eval rho e) = x -> x < 2 ^ 63 -> soff rho e = x.
Proof using .
  intros e x Hx Hr. rewrite soff_snorm. unfold U. rewrite Hx. pose proof (urange (eval rho e)) as Hu.
  apply snorm_id. unfold smin, smax. clear - Hx Hr Hu. lia.
Qed.

Lemma J_soff_lit : forall z : Z, - 2 ^ 63 <= z < 2 ^ 63 -> soff rho (SLit z) = z.
Proof using . intros. apply soff_lit_small. assumption. Qed.

Lemma range_of_rng : forall (o : sobj) (b lo hi : Z),
  bv_unsigned (eval rho (ob_base o)) = b -> soff rho (ob_lo o) = lo -> soff rho (ob_hi o) = hi ->
  obj_range rho o = (b + lo, b + hi).
Proof using . intros o b lo hi Hb Hlo Hhi. unfold obj_range, obj_lo_of, obj_hi_of. rewrite Hb, Hlo, Hhi. reflexivity. Qed.

Lemma rng_stk : forall o : sobj, obj_rng o = ((SVar 1, SLit (- STK_FREE)), SLit 0) ->
  obj_range rho o = (bv_unsigned sp - STK_FREE, bv_unsigned sp).
Proof using HJ argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  intros o Ho. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp) (- STK_FREE) 0); [f_equal; lia| | |].
  - rewrite Hb. apply J_v1. - rewrite Hl. apply J_soff_lit. unfold STK_FREE. lia. - rewrite Hh. apply J_soff_lit. lia.
Qed.

Lemma rng_hdr : forall o : sobj, obj_rng o = ((SVar 1, SLit 0), SLit 16) ->
  obj_range rho o = (bv_unsigned sp, bv_unsigned sp + 16).
Proof using HJ argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  intros o Ho. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp) 0 16); [f_equal; lia| | |].
  - rewrite Hb. apply J_v1. - rewrite Hl. apply J_soff_lit. lia. - rewrite Hh. apply J_soff_lit. lia.
Qed.

Lemma rng_env : forall o : sobj, obj_rng o = ((env_base, SLit 0), SAlu ALU_ADD (sll3 3) (SLit 8)) ->
  obj_range rho o = (bv_unsigned sp + 8 * ARGC + 16, bv_unsigned sp + 8 * ARGC + 16 + 8 * ENVC + 8).
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  intros o Ho. bounds. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp + 8 * ARGC + 16) 0 (8 * ENVC + 8)); [f_equal; lia| | |].
  - rewrite Hb. apply J_env_base. - rewrite Hl. apply J_soff_lit. lia.
  - rewrite Hh. apply J_soff_small; [|lia].
    erewrite J_add; [reflexivity | apply (J_sll3 3 ENVC J_v3); lia | apply J_lit; lia | | |]; lia.
Qed.

(* LPS 727298f3: the auxv object is [auxv_size] bytes (432, or 464 with CONFIG_RSEQ; was 160). *)
Lemma rng_aux : forall o : sobj, obj_rng o = ((aux_base, SLit 0), SLit AUX) ->
  obj_range rho o = (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24, bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24 + AUX).
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  intros o Ho. bounds. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o (bv_unsigned sp + 8 * ARGC + 8 * ENVC + 24) 0 AUX); [f_equal; lia| | |].
  - rewrite Hb. apply J_aux_base. - rewrite Hl. apply J_soff_lit. lia. - rewrite Hh. apply J_soff_lit. lia.
Qed.

Lemma data_lo_hi' : 0 <= data_lo <= data_hi.
Proof using Hdata.
  pose proof Hdata as Hd. unfold data_ok_b in Hd. apply andb_prop in Hd as [Hd _]. apply andb_prop in Hd as [Hd1 Hd2].
  apply Z.leb_le in Hd1. apply Z.leb_le in Hd2. clear - Hd1 Hd2. lia.
Qed.

Lemma rng_data : forall o : sobj, obj_rng o = ((SLit 0, SLit data_lo), SLit data_hi) ->
  obj_range rho o = (data_lo, data_hi).
Proof using Hdata Hdata_hi.
  (* [clear - ..] before each [lia]: a bare [lia] reads the section's Lets (ARGC, STR, ..) and so uses
     [sp] and [inp], which this lemma does not declare. *)
  intros o Ho. pose proof data_lo_hi' as DL. unfold obj_rng in Ho. injection Ho as Hb Hl Hh.
  rewrite (range_of_rng o 0 data_lo data_hi); [f_equal; clear - DL; lia| | |].
  - rewrite Hb. apply J_lit. clear - DL. lia.
  - rewrite Hl. apply J_soff_lit. clear - DL Hdata_hi. lia.
  - rewrite Hh. apply J_soff_lit. clear - DL Hdata_hi. lia.
Qed.

Lemma rng_str0 : obj_range rho O_str0 = (bv_unsigned sp + STR, bv_unsigned sp + STR + Z.of_nat (length argv0) + 1).
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  bounds.
  rewrite (range_of_rng O_str0 (bv_unsigned sp + STR) 0 (Z.of_nat (length argv0) + 1)); [f_equal; lia| | |].
  - apply J_v4. - apply J_soff_lit. lia.
  - cbn [ob_hi O_str0]. apply J_soff_small; [|lia].
    erewrite J_add; [reflexivity | apply J_v5 | apply J_lit; lia | | |]; lia.
Qed.

Lemma rng_rand : obj_range rho O_rand = (bv_unsigned sp + RND, bv_unsigned sp + RND + 16).
Proof using HJ Hinp Hlaunch Hsp pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  bounds.
  rewrite (range_of_rng O_rand (bv_unsigned sp + RND) 0 16); [f_equal; lia| | |].
  - apply J_v6. - apply J_soff_lit. lia. - apply J_soff_lit. lia.
Qed.
End J.

Lemma find_segment_none_high : forall a : word, segs_top segs <= bv_unsigned a ->
  find_segment segs (bv_unsigned a) 1 = None.
Proof using .
  intros a Ha. destruct (find_segment segs (bv_unsigned a) 1) as [seg|] eqn:E; [|reflexivity].
  exfalso. pose proof (find_segment_top segs (bv_unsigned a) 1 seg ltac:(clear - Ha; lia) E) as T. clear - Ha T. lia.
Qed.

Lemma image_byte_none_high : forall a : word, segs_top segs <= bv_unsigned a -> image_byte segs a = None.
Proof using .
  intros a Ha. unfold image_byte, memory_read. rewrite find_segment_none_high by exact Ha. reflexivity.
Qed.

Lemma Jinit_set_rl : forall (rho : valuation) (l : positive) (L : list byte),
  JI rho -> l <> 1%positive -> l <> 2%positive -> JI (rho_set_rl rho l L).
Proof using .
  intros rho l L HJ H1 H2. destruct HJ; constructor; auto.
  - rewrite rho_set_rl_other; auto.
  - rewrite rho_set_rl_other; auto.
Qed.

(* LPS 727298f3: [Jinit] also fixes variable 13 ([ji_execfn], AT_EXECFN's address), so a write keeps it
   only at 14 or above (11 and 12 are free too, but no user writes them). *)
Lemma Jinit_set_rw : forall (rho : valuation) (n : positive) (v : word),
  JI rho -> (14 <= n)%positive -> JI (rho_set_rw rho n v).
Proof using .
  intros rho n v HJ Hn. destruct HJ; constructor; auto; rewrite rho_set_rw_other; auto; clear - Hn; lia.
Qed.

Lemma ms_mem_some_high : forall (ms : machine_state) (a : word) (b : byte),
  segs_top segs <= bv_unsigned a -> wview segs (ms_mem ms) a <> None -> rd ms a = Some b -> ms_mem ms a = Some b.
Proof using .
  intros ms a b Ha Hw Hr. unfold wview in Hw. unfold rd, ms_read_byte in Hr.
  destruct (ms_mem ms a) as [b'|] eqn:E; [exact Hr|].
  rewrite find_segment_none_high in Hw by exact Ha. exfalso. apply Hw. reflexivity.
Qed.

Ltac fwd H := match type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] end.

(* The launch's argv[0] and random-bytes objects, together with the free bytes after argv[0], become
   one strings object [O_strs] over [[sp + str_off, sp + img_len)] whose bytes are [strs_tail].  At
   LPS 727298f3 the random bytes lie below [str_off] (in the head), so [O_rand] is dropped, not merged:
   the tail is argv[0], then free memory. *)
Theorem recarve_strs : forall (rho : valuation) (S : sstate) (tr : list event) (ms : machine_state) (md : Model)
  (A B C D E : sobj) (nv nl : positive),
  smatch segs rho S (tr, mkCfg ms md) -> JI rho ->
  ss_objs S = [A; B; C; D; O_str0; O_rand; E] ->
  obj_rng A = ((SVar 1, SLit (- STK_FREE)), SLit 0) ->
  obj_rng B = ((SVar 1, SLit 0), SLit 16) ->
  obj_rng C = ((env_base, SLit 0), SAlu ALU_ADD (sll3 3) (SLit 8)) ->
  obj_rng D = ((aux_base, SLit 0), SLit AUX) ->
  obj_rng E = ((SLit 0, SLit data_lo), SLit data_hi) ->
  state_has_rl nl S = false -> nl <> 1%positive -> nl <> 2%positive -> (ss_next S <= nv)%positive -> (14 <= nv)%positive ->
  let rho' := rho_set_rw (rho_set_rl rho nl strs_tail) nv (Z_to_bv 64 (LEN - STR)) in
  let S' := mkSS (ss_pc S) (ss_regs S) (ss_fregs S) (ss_fcsr S) (ss_resv S) [A; B; C; D; O_strs nv nl; E]
              (ss_facts S) (Pos.succ nv) (ss_lenient S) in
  swf S' = true ->
  smatch segs rho' S' (tr, mkCfg ms md) /\ JI rho' /\ rl rho' nl = strs_tail /\ rw rho' nv = Z_to_bv 64 (LEN - STR)
  /\ (forall i, i <> nv -> rw rho' i = rw rho i) /\ (forall l, l <> nl -> rl rho' l = rl rho l)
  /\ (forall a, rm rho' a = rm rho a).
Proof using Hdata Hdata_hi Hinp Hlaunch Hsp Htop pc0 ph argv envp ARGC ENVC STR RND PAD LEN AUX argv0.
  intros rho S tr ms md A B C D E nv nl Hsm HJ Hobjs HA HB HC HD HE Hrl Hn1 Hn2 Hnv H7 rho' S' Hwf'.
  pose proof NUMS as NU. pose proof BOUNDS as BD. pose proof stack_max_size_val as SMS.
  pose proof data_lo_hi' as DLH.
  assert (LSB : Z.of_nat (tab argv) <= Z.of_nat (launch_string_bytes argv envp (in_execfn inp)))
    by (unfold launch_string_bytes; rewrite length_flatten_strings; lia).

  set (rho1 := rho_set_rl rho nl strs_tail).
  assert (Hsm1 : smatch segs rho1 S (tr, mkCfg ms md)) by (apply smatch_set_rl; assumption).
  assert (HJ1 : JI rho1) by (apply Jinit_set_rl; assumption).

  assert (Hag : agree_below (ss_next S) rho1 rho') by (apply agree_below_set_rw; exact Hnv).
  assert (Hsm2 : smatch segs rho' S (tr, mkCfg ms md)) by (eapply smatch_agree; [exact Hag | exact Hsm1]).
  assert (HJ' : JI rho') by (apply Jinit_set_rw; assumption).
  assert (Hrl' : rl rho' nl = strs_tail) by (subst rho' rho1; rewrite rho_set_rw_rl, rho_set_rl_at; reflexivity).
  assert (Hrw' : rw rho' nv = Z_to_bv 64 (LEN - STR)) by (subst rho'; apply rho_set_rw_at).
  split; [| split; [exact HJ'|]; split; [exact Hrl'|]; split; [exact Hrw'|]].
  2:{ subst rho' rho1. split; [|split].
      - intros i Hi. rewrite rho_set_rw_other by exact Hi. reflexivity.
      - intros l Hl. rewrite rho_set_rw_rl, rho_set_rl_other by exact Hl. reflexivity.
      - intros a. rewrite rho_set_rw_rm, rho_set_rl_rm. reflexivity. }

  pose proof Hsm2 as (_ & _ & _ & _ & Hrom & Hroc & _ & _ & _ & _ & Hmm & _). cbn [fst snd cfg_ms cfg_model] in Hmm, Hrom, Hroc.
  rewrite Hobjs in Hmm. destruct Hmm as (Hall & Hpd & Hfr).
  pose proof Hall as Hall0.
  fwd Hall. fwd Hall. fwd Hall. fwd Hall. fwd Hall. fwd Hall. fwd Hall. clear Hall.
  rename H into HoA. rename H0 into HoB. rename H1 into HoC. rename H2 into HoD.
  rename H3 into Ho0. rename H4 into HoR. rename H5 into HoE.
  pose proof (rng_stk rho' HJ' A HA) as RA. pose proof (rng_hdr rho' HJ' B HB) as RB.
  pose proof (rng_env rho' HJ' C HC) as RC. pose proof (rng_aux rho' HJ' D HD) as RD.
  pose proof (rng_data rho' E HE) as RE.
  pose proof (rng_str0 rho' HJ') as R0. pose proof (rng_rand rho' HJ') as RR.
  assert (Hb4 : bv_unsigned (eval rho' (SVar 4)) = bv_unsigned sp + STR) by (apply J_v4; exact HJ').
  assert (Hhi : soff rho' (SVar nv) = LEN - STR).
  { apply (J_soff_small rho'); [|lia]. cbn [eval]. rewrite Hrw'. apply U_addr. lia. }
  assert (RS : obj_range rho' (O_strs nv nl) = (bv_unsigned sp + STR, bv_unsigned sp + LEN)).
  { rewrite (range_of_rng rho' (O_strs nv nl) (bv_unsigned sp + STR) 0 (LEN - STR)); [f_equal; lia | exact Hb4 | apply soff_lit_small; lia | exact Hhi]. }

  assert (PR : forall off, 0 <= off < LEN - STR ->
            ms_mem ms (Z_to_bv 64 (bv_unsigned sp + STR + off)) = Some (nth (Z.to_nat off) strs_tail (Z_to_bv 8 0))).
  { intros off Hoff.
    assert (Htopa : segs_top segs <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + STR + off))) by (rewrite U_addr by lia; lia).
    destruct (Z_lt_le_dec off (Z.of_nat (length argv0) + 1)) as [Hlt|Hge].
    -
      pose proof Ho0 as (_ & Hw & _ & Hd & _).
      unfold obj_lo_of, obj_hi_of in Hw, Hd. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells O_str0] in Hw, Hd.
      rewrite Hb4 in Hw, Hd.
      assert (Hlo0 : soff rho' (SLit 0) = 0) by (apply soff_lit_small; lia).
      assert (Hhi0 : soff rho' (SAlu ALU_ADD (SVar 5) (SLit 1)) = Z.of_nat (length argv0) + 1).
      { apply (J_soff_small rho'); [|lia]. erewrite (J_add rho'); [reflexivity | apply J_v5; exact HJ' | apply (J_lit rho'); lia | | |]; lia. }
      rewrite Hlo0, Hhi0 in Hw, Hd.
      apply ms_mem_some_high; [exact Htopa | apply Hw; [lia|reflexivity] |].
      cbn [dflt_holds] in Hd. rewrite (Hd off ltac:(lia) ltac:(intros HC0; inversion HC0)).
      rewrite (ji_str0 _ _ _ _ _ _ _ _ HJ'). rewrite Z.sub_0_r. f_equal. symmetry. apply tail_nth_str0. lia.
    -
      rewrite Hfr.
      * subst rho' rho1. rewrite rho_set_rw_rm, rho_set_rl_rm. rewrite (ji_mem _ _ _ _ _ _ _ _ HJ).
        replace (bv_unsigned sp + STR + off) with (bv_unsigned sp + (Z.of_nat (str_off inp sp draw) + Z.of_nat (Z.to_nat off))) by (subst STR; lia).
        apply (ms0_mem_region segs pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch _ strs_tail (Z.to_nat off) region_tail).
        pose proof length_tail. lia.
      * unfold outside_all. repeat apply Forall_cons; try apply Forall_nil;
          rewrite ?RA, ?RB, ?RC, ?RD, ?RE, ?R0, ?RR; cbn [fst snd]; rewrite U_addr by lia; unfold STK_FREE; lia. }
  (* The random bytes [[sp + rand_off, + 16)]: [O_rand]'s cells hold the launch's two random words. *)
  assert (PRR : forall d, 0 <= d < 16 ->
            ms_mem ms (Z_to_bv 64 (bv_unsigned sp + RND + d)) = Some (nth (Z.to_nat d) (rand_bytes draw) (Z_to_bv 8 0))).
  { intros d Hd16.
    assert (Htopa : segs_top segs <= bv_unsigned (Z_to_bv 64 (bv_unsigned sp + RND + d))) by (rewrite U_addr by lia; lia).
    pose proof HoR as (_ & Hw & Hc & _ & _).
    unfold obj_lo_of, obj_hi_of in Hw, Hc. cbn [ob_base ob_lo ob_hi ob_dflt ob_cells O_rand] in Hw, Hc.
    rewrite (J_v6 rho' HJ') in Hw.
    rewrite !soff_lit_small in Hw by lia.
    set (k := Z.to_nat (d / 8)). set (i := Z.to_nat (d mod 8)).
    assert (Hk : (k < 2)%nat) by (subst k; clear - Hd16; Z.to_euclidean_division_equations; lia).
    assert (Hi8 : (i < 8)%nat) by (subst i; pose proof (Z.mod_pos_bound d 8 ltac:(lia)); lia).
    assert (Hdki : d = 8 * Z.of_nat k + Z.of_nat i).
    { subst k i. rewrite !Z2Nat.id by (try apply Z.div_pos; try apply Z.mod_pos_bound; lia).
      rewrite <- Z.div_mod; lia. }
    apply Forall_cons_iff in Hc as [Hc0 Hc]. apply Forall_cons_iff in Hc as [Hc1 _].
    assert (HCK : cell_holds rho' (SVar 6) 0 16 ms (cell8 (8 * Z.of_nat k) (SVar (Pos.of_nat (9 + k))))).
    { destruct k as [|[|k]]; [exact Hc0 | exact Hc1 | lia]. }
    destruct HCK as (_ & _ & HR). unfold cell8 in HR. cbn [c_off c_width c_val eval] in HR.
    rewrite soff_lit_small in HR by lia. change (Z.to_nat 8) with 8%nat in HR.
    unfold oaddr in HR. cbn [eval] in HR. rewrite (ji_rand _ _ _ _ _ _ _ _ HJ') in HR.
    change (Z.of_nat (rand_off inp)) with RND in HR.
    rewrite (U_addr (bv_unsigned sp + RND)) in HR by lia.
    apply ms_mem_some_high; [exact Htopa | apply Hw; [lia|reflexivity] |].
    rewrite Hdki.
    replace (bv_unsigned sp + RND + (8 * Z.of_nat k + Z.of_nat i))
      with (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + RND + 8 * Z.of_nat k)) + Z.of_nat i)
      by (rewrite U_addr by lia; lia).
    rewrite (rd_bytes_nth ms 8 _ _ i HR Hi8) by (rewrite U_addr by lia; lia).
    f_equal. symmetry.
    replace (Z.to_nat (8 * Z.of_nat k + Z.of_nat i)) with (8 * k + i)%nat by lia.
    rewrite (rand_bytes_nth k i Hk Hi8).
    do 3 f_equal. symmetry.
    destruct k as [|[|k]]; [ | | lia]; cbn [nth Nat.add Pos.of_nat];
      [exact (ji_rnd0 _ _ _ _ _ _ _ _ HJ') | exact (ji_rnd1 _ _ _ _ _ _ _ _ HJ')]. }
  apply (smatch_set_objs_next segs rho' S (tr, mkCfg ms md) [A; B; C; D; O_strs nv nl; E] (Pos.succ nv) (ss_lenient S) Hsm2); [|exact Hwf'].
  cbn [snd cfg_ms].
  split; [|split].
  -
    repeat apply Forall_cons; try assumption; try apply Forall_nil.
    apply (obj_holds_of segs rho' ms (O_strs nv nl) (bv_unsigned sp + STR) 0 (LEN - STR));
      cbn [ob_base ob_lo ob_hi ob_cells ob_dflt O_strs].
    + exact Hb4.
    + apply soff_lit_small. lia.
    + exact Hhi.
    + lia.
    + intros off Hoff _. unfold wview. rewrite (PR off Hoff). discriminate.
    + constructor.
    + intros off Hoff _. cbn [dflt_holds]. unfold rd, ms_read_byte. rewrite (PR off Hoff), Hrl', Z.sub_0_r. reflexivity.
    + cbn [dflt_inv]. rewrite Hrl', length_tail. lia.
  -
    unfold pairwise_disjoint.
    repeat split; repeat (apply Forall_cons || apply Forall_nil);
      rewrite ?RA, ?RB, ?RC, ?RD, ?RE, ?RS; unfold ranges_disjoint, STK_FREE; cbn [fst snd]; try lia.
  -
    (* Outside every object of [S']: either outside every old object (the old frame), or in the random
       bytes, which [O_rand] no longer covers but which [ms] still holds as the launch image does. *)
    intros a Ha. unfold outside_all in Ha.
    fwd Ha. fwd Ha. fwd Ha. fwd Ha. fwd Ha. fwd Ha. clear Ha.
    rewrite RS in H3. cbn [fst snd] in H3.
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp + RND)) as [L1|L1];
      [|destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned sp + RND + 16)) as [L2|L2]].
    2:{ pose proof (urange a) as UA.
        set (d := bv_unsigned a - (bv_unsigned sp + RND)).
        assert (Ea : a = Z_to_bv 64 (bv_unsigned sp + RND + d)) by (apply bv_eq; rewrite U_addr by lia; subst d; lia).
        rewrite Ea, (PRR d ltac:(subst d; lia)).
        subst rho' rho1. rewrite rho_set_rw_rm, rho_set_rl_rm. rewrite (ji_mem _ _ _ _ _ _ _ _ HJ).
        replace (bv_unsigned sp + RND + d) with (bv_unsigned sp + (Z.of_nat (rand_off inp) + Z.of_nat (Z.to_nat d))) by (subst RND; lia).
        rewrite (ms0_mem_region segs pc0 ph sp brk mb draw inp Hsp Hinp Hlaunch _ (rand_bytes draw) (Z.to_nat d) region_rnd)
          by (rewrite length_rand_bytes; lia).
        reflexivity. }
    all: apply Hfr; unfold outside_all; repeat apply Forall_cons; try apply Forall_nil; try assumption;
      rewrite ?R0, ?RR; cbn [fst snd]; lia.
Qed.
End Strs.
