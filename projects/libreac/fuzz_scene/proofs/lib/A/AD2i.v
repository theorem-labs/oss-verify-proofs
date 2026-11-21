(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and lib/A/AD2j.v for libreac/fuzz_scene's asan image (sha256 43654a025fd0...) by a Theorem Labs lane's gen_ad2.py, with its module paths changed: sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/A/AB01.v, the image bounds from lib/A/AB12.v and the rw window 0x9d000..0x5f9000; IMG_REGIONS below .data from the image and the owned static cells of the generated lib/A/AF0m.v; owned static cells come from the GENERATED f0mgen2 AF0m (af0m.py, --base the hand-assembled reference) *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 in the shared CONFIG_RSEQ-parameterised form of reac-pw/fuzz_segconf's copy of this file (spellings, VT, cjust, rjust and entry_check over the flag; entry_check_all over each flag's computed hand-off states; the start state's stack write depth; the gap word and the pad of the top-anchored launch stack), with this unit's addresses and the thread-id and canary variables 47 and 64 read from its own probes; launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef). *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YK1b.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YK0h.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require PlanRegen.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.libreac.fuzz_scene.images Require Import Asan.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YP0m YP09 YP0l YP08 YP03 YN3q YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.A Require Import AB12 AB1h AB13 AB01r AD2j.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YD1h.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Open Scope Z_scope.
Definition eSp0 : expr := EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EMd M_MUL (ELit 16) (EVar 6)).
Lemma eSp0_e_sp0 : eSp0 = e_sp0.
Proof. reflexivity. Qed.
Definition B5 : expr :=
EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
(EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6)))).
(* LPS 727298f3: the strings sit at the top of the stack and the block below them is
   [StackLayout.block_head_size] bytes, flag-dependent (the auxv is 27 or 29 pairs), with the
   gap word [V_G] (EVar 9) and the pad bytes [V_W] (EVar 4, a byte count now).  So argv[0] is
   [BS + HEAD rz], argv[1] is [argv[0] + V_L0 + 1], and the AT_RANDOM bytes are [BR + HEAD rz - 16],
   at the run's own CONFIG_RSEQ flag [rz] ([HEAD rz] is [block_head_size] less the argv/envp words, the gap
   word and the pad, StackLayout.v).  Every computed hand-off state of [AB01r] holds them at [eSp0 + 8] and
   [eSp0 + 16], at both flags: [entry_check_all] checks it by computation (read from this unit's hand-off probe; the record is kept outside the tree with the probe text). *)
Definition HEAD (rz : Z) : Z := 472 + 32 * rz.
Definition BS : expr :=
EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
(EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9)))))).
Definition eArgv1 (rz : Z) : expr :=
EMd M_MUL (EAlu ALU_SLTU (ELit 1) (EVar 1))
(EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
(EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))))))
(ELit (HEAD rz + 1))).
Definition BR : expr :=
EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0))
(EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))).
Lemma auxv_bytes_rz : forall b, AUXV_BYTES b = 432 + 32 * rseq_z b.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma z_argv1_eq : forall t (av ev : list (list byte)) efn, (1 <= length av)%nat ->
z_argv t av ev efn 1 = z_strs t av ev efn + Z.of_nat (length (nth 0 av [])) + 1.
Proof.
intros t av ev efn H. unfold z_argv. destruct av as [|a0 r]; [cbn in H; lia|].
change (firstn 1 (a0 :: r)) with [a0]. change (nth 0 (a0 :: r) []) with a0.
unfold total_arg_bytes_nat. cbn [fold_right]. rewrite Nat.add_0_r, Nat2Z.inj_add, Z.add_assoc. reflexivity.
Qed.
Definition eEnvp : expr :=
EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EMd M_MUL (ELit 16) (EVar 6)))) (ELit 16).
Definition spellings (rz : Z) (ob : option nat) : list (expr * Z) :=
match ob with
| None => [(ELit 0, 0)]
| Some 0%nat => [(eSp0, 0)]
| Some 5%nat => [(B5, 24)]
| Some 6%nat => [(BR, HEAD rz - 16)]
| _ => []
end.
(* LPS 727298f3: the thread-id variable and the canary's variable of the computed hand-off states
   (the released 43 and 60 named the recorded states' variables; the start-up renumbering of
   A/AB01r.v, +4 from 10 below 391, read from this unit's start-up probe, moves them to 47 and 64).  Every
   computed state, at both CONFIG_RSEQ flags, holds [KRange (EVar 47) 1 4194303] and [EVar 64] at both canary
   cells of [IMG_REGIONS] (the [SOff CANARY_ATOM 0] chunks): [entry_check_all] checks it by computation
   (read from this unit's hand-off probe; the record is kept outside the tree with the probe text). *)
Definition TIDV : nat := 47.
Definition CANV : nat := 64.
Definition CANARY_ATOM : nat := 41.
Definition VT (two : bool) (rz : Z) : list (expr * sv) :=
[ (EVar 1, SOff 3 0); (EVar TIDV, SOff 8 0); (EExt false 0 4 (EVar TIDV), SOff 8 0);
(EAlu ALU_ADD BS (ELit (HEAD rz)), SOff 1 0); (EAlu ALU_ADD B5 (ELit 24), SOff 5 0);
(EVar 8, SData UID_DATOM 0 8); (EVar CANV, SOff CANARY_ATOM 0);
(EAlu ALU_ADD eSp0 (ELit (-48)), SOff 0 (-48)); (EAlu ALU_ADD eSp0 (ELit 8), SOff 0 8); (eEnvp, SOff 4 0) ]
++ (if two then [(eArgv1 rz, SOff 2 0)] else []).
Definition vmatch (two : bool) (rz : Z) (v : expr) (s : sv) : bool :=
match v, s with
| ELit z, SLit z' => Z.eqb z z'
| _, _ => existsb (fun p => expr_eqb (fst p) v && sv_eqb (snd p) s)%bool (VT two rz)
end.
Definition sregs_main : list sv :=
[ SLit 0; SLit 568100; SOff 0 (-48); SLit 67584; SLit 6121368; SOff 14 0; SOff 15 0; SOff 16 0;
SOff 0 8; SOff 3 0; SOff 3 0; SOff 0 8; SOff 4 0; SOff 22 0; SOff 23 0; SOff 24 0;
SOff 25 0; SOff 26 0; SLit 533464; SOff 4 0; SLit 0; SLit 0; SLit 0; SLit 0;
SLit 0; SLit 0; SLit 0; SLit 0; SOff 37 0; SOff 38 0; SOff 39 0; SOff 40 0 ].
Definition rcheck (two : bool) (rz : Z) (ch : acs) (i : nat) : bool :=
let s := nth i sregs_main (SLit 0) in let e := nth i (s_regs (a_ss ch)) (ELit 0) in
(match s with SOff n 0 => (n =? 9 + i)%nat | _ => false end || vmatch two rz e s)%bool.
Definition wok (w : N) : bool := ((w =? 1) || (w =? 2) || (w =? 4) || (w =? 8))%N.
Definition cjust (two : bool) (rz : Z) (ch : acs) (ob : option nat) (c : YP09.chunk) : bool :=
existsb (fun sp : expr * Z => let (rb, d) := sp in
match YP09.c_val c with
| CVal w s => (wok w && match kn_read TSEGS ch rb (YP09.c_off c + d) (N.to_nat w) with Some v => vmatch two rz v s | None => false end)%bool
| CZero l => kn_zcover TFIB_BSS ch rb (YP09.c_off c + d) l
| CImg l => match ob with
| None => (kn_img ch (YP09.c_off c) l && (0x10000 <=? YP09.c_off c) && (YP09.c_off c + l <=? 0x5f9000) && (0 <=? l))%bool
| Some _ => false end
| CData _ _ _ => false
end) (spellings rz ob).
(* 727298f3: the start state's stack write fact is [KWr (SA e_sp0 (-stack_window_depth)) (ELit stack_window_depth)]
   (Reusable/YK09.v:2762, [init_kn_with]), where [stack_window_depth = stack_max_size - stack_window_reach]
   = 8388608 - 2244095 (Reusable/YK1b.v:117-122); the released 8388608 was the whole [stack_max_size].
   Every computed hand-off state holds it: [entry_check_all] checks it by computation. *)
Definition WDEPTH : Z := 6144513.
Lemma WDEPTH_eq : WDEPTH = YK1b.stack_window_depth.
Proof. reflexivity. Qed.
Definition KWR_STACK : kentry := KWr (SA eSp0 (- WDEPTH)) (ELit WDEPTH).
Section f.
Variable E : env.
#[local] Notation u := (uE E).
#[local] Notation V n := (bv_unsigned (ev E n)).
Lemma uE_bound : forall e, 0 <= u e < 2 ^ 64.
Proof. intros e. unfold uE. pose proof (bv_unsigned_in_range 64 (edenot E e)) as H. change (bv_modulus 64) with (2 ^ 64) in H. lia. Qed.
Lemma eqm_small_eq : forall a b, eqm a b -> 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> a = b.
Proof. intros a b [q Hq] Ha Hb. assert (q = 0) by nia. subst q. lia. Qed.
Lemma uE_litv : forall z, 0 <= z < 2 ^ 64 -> u (ELit z) = z.
Proof. intros z Hz. unfold uE. cbn [edenot]. rewrite u64_lit by lia. reflexivity. Qed.
Lemma uE_var : forall n, u (EVar n) = V n.
Proof. reflexivity. Qed.
Lemma uE_add : forall a b, u a + u b < 2 ^ 64 -> u (EAlu ALU_ADD a b) = u a + u b.
Proof.
intros a b H. pose proof (uE_bound a). pose proof (uE_bound b). pose proof (uE_bound (EAlu ALU_ADD a b)).
apply eqm_small_eq; [|lia|lia]. unfold uE. cbn [edenot]. apply u_add_eqm.
Qed.
Lemma uE_add_eqm : forall a b, eqm (u (EAlu ALU_ADD a b)) (u a + u b).
Proof. intros a b. unfold uE. cbn [edenot]. apply u_add_eqm. Qed.
Lemma uE_mul_lit : forall k a, 0 <= k -> k * u a < 2 ^ 64 -> u (EMd M_MUL (ELit k) a) = k * u a.
Proof.
intros k a Hk H. pose proof (uE_bound a). pose proof (uE_bound (EMd M_MUL (ELit k) a)).
assert (Hk' : k < 2 ^ 64 \/ u a = 0) by nia.
apply eqm_small_eq; [|lia|nia]. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_mul_eqm|]. fold (u a). destruct Hk' as [Hk'|Hz].
- rewrite u64_lit by lia. apply eqm_refl.
- rewrite Hz, !Z.mul_0_r. apply eqm_refl.
Qed.
Lemma uE_add_negmul : forall a k b, - 2 ^ 64 < k < 0 -> - k * u b <= u a -> u (EAlu ALU_ADD a (EMd M_MUL (ELit k) b)) = u a + k * u b.
Proof.
intros a k b Hk H. pose proof (uE_bound a). pose proof (uE_bound b). pose proof (uE_bound (EAlu ALU_ADD a (EMd M_MUL (ELit k) b))).
apply eqm_small_eq; [|lia|nia]. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_add_eqm|]. fold (u a). apply eqm_add; [apply eqm_refl|].
eapply eqm_trans; [apply u_mul_eqm|]. fold (u b). apply eqm_mul_r. apply eqm_u_lit.
Qed.
Lemma uE_add_neglit : forall a k, k < 0 -> - k <= u a -> u (EAlu ALU_ADD a (ELit k)) = u a + k.
Proof.
intros a k Hk H. pose proof (uE_bound a). pose proof (uE_bound (EAlu ALU_ADD a (ELit k))).
apply eqm_small_eq; [|lia|lia]. unfold uE. cbn [edenot].
eapply eqm_trans; [apply u_add_eqm|]. fold (u a). apply eqm_add; [apply eqm_refl|]. apply eqm_u_lit.
Qed.
Lemma uE_and_lit : forall a k, 0 <= k < 2 ^ 64 -> u (EAlu ALU_AND a (ELit k)) = Z.land (u a) k.
Proof.
intros a k Hk. unfold uE. cbn [edenot]. rewrite u_and64. f_equal. apply u64_lit. lia.
Qed.
End f.
Definition WSTK : Z := 65536.
Definition wjust (ch : acs) (r : YP09.region) : bool :=
((r_whi r <=? r_wlo r)
|| match r_base r with
| None => (0x9d000 <=? r_wlo r) && (r_whi r <=? 0x5f9000)
| Some 0%nat => kn_mem KWR_STACK ch && (- WDEPTH <=? r_wlo r) && (r_whi r <=? 0)
| Some _ => false
end)%bool.
Definition rjust (two : bool) (rz : Z) (ch : acs) (r : YP09.region) : bool :=
(forallb (cjust two rz ch (r_base r)) (r_chunks r) && wjust ch r
&& match r_base r with None => (0 <=? r_lo r) && (r_hi r <=? 2 ^ 47) | Some 0%nat => (- 2 ^ 40 <=? r_lo r) && (r_hi r <=? 2 ^ 40)
| Some 6%nat => (0 <=? r_lo r) && (r_hi r <=? 16) | _ => false end)%bool.
Definition R_stk : YP09.region := YP09.mkRegion (Some 0%nat) (- WSTK) 0 (- WSTK) 0 [].
Definition TFIB_MAIN : Z := 0x823d8.
Definition entry_check (two : bool) (rz : Z) (ch : acs) : bool :=
(kn_mem (KRange (EVar TIDV) 1 4194303) ch
&& forallb (rjust two rz ch) (R_stk :: R_hdr two :: IMG_REGIONS)
&& forallb (rcheck two rz ch) (seq 0 32)
&& afd_eqb (a_fd ch) FdStd && Z.eqb (pc ch) TFIB_MAIN)%bool.
(* LPS 727298f3: each flag's hand-off states are checked at that flag's spellings. *)
Lemma entry_check_all : forall b, forallb (fun ch => entry_check true (rseq_z b) ch && entry_check false (rseq_z b) ch)
(HS_tfib_list_r (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma HS_tfib_r_In_r : forall r h ch, HS_tfib_r r h = Some ch -> In ch (HS_tfib_list_r r).
Proof.
intros r h ch H. unfold HS_tfib_r, PlanRegen.hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _].
unfold HS_tfib_list_r. exact (in_map snd _ _ F).
Qed.
Definition stack_strs (av ev : list (list byte)) (efn : list byte) : list byte :=
flatten_strings av ++ flatten_strings ev ++ efn ++ [Z_to_bv 8 0].
Definition runs_main_tfa (two : bool) (sp top : word) (av ev : list (list byte)) (efn : list byte) : list (Z * list byte) :=
(z_envp (bv_unsigned sp) av, envp_block top av ev efn)
:: (z_argv (bv_unsigned top) av ev efn 0, nth 0 av [] ++ [NUL])
:: (if two then [(z_argv (bv_unsigned top) av ev efn 1, nth 1 av [] ++ [NUL])] else [])
++ [(z_strs (bv_unsigned top) av ev efn, stack_tail av ev efn)].
Section g. Context {fx : YK11.FPState}.
Section t.
Variables (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Hypothesis Hvl : valid_launch inp.
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
Hypothesis Hvi : valid_input inp.
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
(* SINV stays abstract at the packed-input boundary. YA02's rseq alias retains
   the complete input-field spine; instantiate it from inp rather than copying
   the donor's shortened argument list. HM uses the same packed input as YP08.m0. *)
Variable SINV : env -> (word -> option byte) -> Prop.
#[local] Notation argH := (YA02.argH0 sp rdraw argv envp
  (in_image_fs inp) (in_stdin inp) uid (in_gid inp) hw (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
#[local] Notation entryw := (Z_to_bv 64 (Z.of_N Asan.M.init_pc)).
Hypothesis SINV_sp0 : forall E' M, SINV E' M -> uE E' e_sp0 = TOP + 8388608.
Hypothesis HC : cs_ok TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk argv envp
  (in_image_fs inp) (in_stdin inp) uid (in_gid inp) hw (in_groups inp) (in_net inp)
  (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp) (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem inp mbase TPH entryw sp rdraw a.
Hypothesis SL_allowed : forall a, sliverb sp a = true -> page_allowedb (allowA TFIB E ch) (page_base a) = true.
#[local] Notation MR := (Mr TFIB TOP argH E ch model FULL).
#[local] Notation HID := (hid TFIB TOP argH E ch model).
Let TOPok : top_ok TOP := YA02.top_ok0 sp Hsp.
(* The exported bound proof retains the image entry before Hsp and Hva. *)
Let ARGH : forall E0 (a : word), argH E0 a = true -> TOP <= bv_unsigned a.
Proof.
  (* As A/AD1g.v: [YA02.argH0_high] also abstracts [apc]. *)
  intros E0 a H. unshelve eapply (YA02.argH0_high sp rdraw argv envp
    (in_image_fs inp) (in_stdin inp) uid (in_gid inp) hw (in_groups inp) (in_net inp)
    (in_nofile inp) (in_sigmask inp) (in_urandom inp) (in_tmp inp)
    (in_kernel inp) (in_execfn inp) (in_sigpipe_default inp)); try exact H; try exact Hva; try exact Hsp; try exact 0%N.
Qed.
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
(* The TOP-anchored stack: [z_strs]/[z_argv]/[z_envs]/[z_execfn] count down from [ztop],
   while [z_envp]/[z_auxv]/[z_rand] stay on [zsp] (YP08.v:196-207 against YP08.v:504-505).
   [z_rand] also gained the run's own rseq flag as its second argument (YP08.v:199). *)
#[local] Notation efn := (in_execfn inp).
#[local] Notation krs := (kb_rseq (in_kernel inp)).
#[local] Notation RZ := (rseq_z krs).
#[local] Notation ztop := (bv_unsigned (ed_top rdraw)).
Definition xwE (n : nat) : word :=
match n with
| 8%nat => ev E TIDV
| _ => if ((9 <=? n) && (n <=? 40))%nat then getr R (Z_to_bv 5 (Z.of_nat (n - 9)))
else if (n =? CANARY_ATOM)%nat then ev E CANV else Z_to_bv 64 0
end.
(* YP08's Proof Using All exports every auxiliary-vector data atom, even on the
   argv-region and initial-facts lemmas. Each value comes from this launch. *)
Definition xdE (d : nat) : list byte :=
if Nat.eqb d UID_DATOM then uid_bytes (in_uid inp)
else if Nat.eqb d HWCAP_DATOM then hwcap_bytes (in_hwcap inp)
else if Nat.eqb d RAND_DATOM then rand_bytes rdraw
else if Nat.eqb d GID_DATOM then gid_bytes (in_gid inp)
else if Nat.eqb d EHDR_DATOM then ehdr_bytes inp sp mbase
else if Nat.eqb d EXECFN_DATOM then execfn_ptr_bytes (ed_top rdraw) (in_execfn inp)
else [].
Lemma xdE_uid : xdE UID_DATOM = uid_bytes (in_uid inp). Proof. reflexivity. Qed.
Lemma xdE_hwcap : xdE HWCAP_DATOM = hwcap_bytes (in_hwcap inp). Proof. reflexivity. Qed.
Lemma xdE_rand : xdE RAND_DATOM = rand_bytes rdraw. Proof. reflexivity. Qed.
Lemma xdE_gid : xdE GID_DATOM = gid_bytes (in_gid inp). Proof. reflexivity. Qed.
Lemma xdE_ehdr : xdE EHDR_DATOM = ehdr_bytes inp sp mbase. Proof. reflexivity. Qed.
Lemma xdE_execfn : xdE EXECFN_DATOM = execfn_ptr_bytes (ed_top rdraw) (in_execfn inp).
Proof. reflexivity. Qed.
Definition EL : YP0m.env :=
YP08.E0 sp (ed_top rdraw) (kb_rseq (in_kernel inp)) argv envp efn xwE xdE.
Lemma ev1 : bv_unsigned (ev E 1) = Z.of_nat (length argv).
Proof.
rewrite (HE 1%nat) by (unfold NX0G; lia). cbn. apply u64_lit. pose proof (proj1 Hva). lia.
Qed.
Lemma ev2 : bv_unsigned (ev E 2) = Z.of_nat (length envp).
Proof.
rewrite (HE 2%nat) by (unfold NX0G; lia). cbn. apply u64_lit. pose proof (proj1 Hve). lia.
Qed.
Lemma ev3 : bv_unsigned (ev E 3) = Z.of_nat (length (nth 0 argv [])).
Proof.
rewrite (HE 3%nat) by (unfold NX0G; lia). cbn. apply u64_lit.
pose proof Hva as (L & _ & F & _). revert L F. generalize (in_argv inp) as av. intros av L F.
destruct av as [|a0 r]; cbn in *; [lia|]. inversion F; subst. cbn in *. lia.
Qed.
Lemma ev8 : ev E 8 = in_uid inp.
Proof. rewrite (HE 8%nat) by (unfold NX0G; lia). reflexivity. Qed.
(* [V_G] (EVar 9), STACK_ROUND's gap word count (Reusable/YA02.v [G]). *)
Lemma ev9 : bv_unsigned (ev E 9) = Z.of_nat (block_items argv envp mod 2).
Proof.
rewrite (HE 9%nat) by (unfold NX0G; lia).
change (bv_unsigned (Z_to_bv 64 (Z.of_nat (block_items argv envp mod 2))) = Z.of_nat (block_items argv envp mod 2)).
apply u64_lit. pose proof (YP08.yp_gap_range argv envp). lia.
Qed.
Lemma ev4 : bv_unsigned (ev E 4)
= Z.of_nat (block_pad_len krs sp (ed_top rdraw) argv envp efn).
Proof.
rewrite (HE 4%nat) by (unfold NX0G; lia).
change (bv_unsigned (Z_to_bv 64 (Z.of_nat (block_pad_len krs sp (ed_top rdraw) argv envp efn)))
= Z.of_nat (block_pad_len krs sp (ed_top rdraw) argv envp efn)).
apply u64_lit.
pose proof (YP08.yp_pad_eq TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as HP.
pose proof (YP08.top_le TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as HT.
pose proof (u64_range sp).
pose proof (Nat2Z.is_nonneg (block_head_size krs argv envp)).
pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp efn)).
pose proof (Nat2Z.is_nonneg (block_pad_len krs sp (ed_top rdraw) argv envp efn)).
unfold SP_HI in HT. lia.
Qed.
Lemma CHK : forall two, entry_check two RZ ch = true.
Proof.
intros two. pose proof (proj1 (forallb_forall _ _) (entry_check_all krs) ch (HS_tfib_r_In_r _ h ch Hch)) as H. cbn beta in H.
apply andb_prop in H as [H1 H2]. destruct two; [exact H1 | exact H2].
Qed.
Lemma CHK_parts : forall two,
kn_mem (KRange (EVar TIDV) 1 4194303) ch = true /\ forallb (rjust two RZ ch) (R_stk :: R_hdr two :: IMG_REGIONS) = true
/\ forallb (rcheck two RZ ch) (seq 0 32) = true /\ a_fd ch = FdStd /\ pc ch = TFIB_MAIN.
Proof.
intros two. pose proof (CHK two) as H. unfold entry_check in H.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|apply Z.eqb_eq; exact H5].
destruct (a_fd ch); [reflexivity | discriminate H4 | discriminate H4].
Qed.
Lemma tid_range : 1 <= bv_unsigned (ev E TIDV) <= 4194303.
Proof.
pose proof (ho_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC (EVar TIDV) 1 4194303) as X.
unfold uE in X. apply X. exact (proj1 (CHK_parts true)).
Qed.
Lemma EL0 : bv_unsigned (ew EL 0) = usp.   Proof. reflexivity. Qed.
Lemma EL1 : bv_unsigned (ew EL 1) = z_strs ztop argv envp efn.
Proof. unfold EL. exact (YP08.ew1 TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE). Qed.
Lemma EL2 : (2 <= length argv)%nat -> bv_unsigned (ew EL 2) = z_argv ztop argv envp efn 1.
Proof. unfold EL. exact (YP08.ew2' TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE). Qed.
Lemma EL3 : bv_unsigned (ew EL 3) = Z.of_nat (length argv).
Proof. unfold EL. exact (YP08.ew3 TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE). Qed.
Lemma EL4 : bv_unsigned (ew EL 4) = z_envp usp argv.
Proof. unfold EL. exact (YP08.ew4 TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE). Qed.
Lemma EL5 : bv_unsigned (ew EL 5) = z_auxv usp argv envp.
Proof. unfold EL. exact (YP08.ew5 TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE). Qed.
Lemma EL6 : bv_unsigned (ew EL 6) = z_rand usp krs argv envp.
Proof. unfold EL. exact (YP08.ew6 TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE). Qed.
Lemma EL8 : ew EL 8 = ev E TIDV.   Proof. reflexivity. Qed.
Lemma EL41 : ew EL CANARY_ATOM = ev E CANV.   Proof. reflexivity. Qed.
Lemma ELF : forall n, (9 <= n <= 40)%nat -> ew EL n = getr R (Z_to_bv 5 (Z.of_nat (n - 9))).
Proof.
intros n Hn. unfold EL, YP08.E0. cbn [ew].
destruct n as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; try lia. unfold xwE.
replace ((9 <=? S (S (S (S (S (S (S (S (S n))))))))) && (S (S (S (S (S (S (S (S (S n)))))))) <=? 40))%nat with true
by (symmetry; apply andb_true_iff; split; apply Nat.leb_le; lia). reflexivity.
Qed.
(* [layout_facts] is EIGHT conjuncts at 75d69e00 (YP08.v:753-762) and no longer carries
   [z_rand + 16 < 2^63]; the surviving form of that one is [YP08.z_rand_end] (YP08.v:695).
   Conjuncts 4+6+7 chain [z_rand + 16 <= z_strs <= ztop <= SP_HI]. *)
Let LF : z_envp usp argv = usp + 16 + 8 * Z.of_nat (length argv)
/\ z_auxv usp argv envp = z_envp usp argv + 8 * Z.of_nat (length envp) + 8
/\ z_rand usp krs argv envp = z_auxv usp argv envp + AUXV_BYTES krs + 8 * Z.of_nat (block_items argv envp mod 2)
/\ z_rand usp krs argv envp + 16 <= z_strs ztop argv envp efn
/\ z_argv ztop argv envp efn 0 = z_strs ztop argv envp efn
/\ z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv) + Z.of_nat (total_arg_bytes_nat envp)
+ Z.of_nat (length efn) + 1 + 8 = ztop
/\ ztop <= SP_HI
/\ SP_LO <= usp <= SP_HI.
Proof. exact (YP08.layout_facts TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau). Qed.
(* The eight conjuncts, named by MEANING rather than by position: [layout_facts] went from
   seven conjuncts to eight at 75d69e00, and a positional [pose proof LF as (L1 & .. & L7)]
   is exactly the pattern that silently mis-binds when a conjunct is added.  [tauto] picks
   the conjunct, so none of these is counting-dependent. *)
Let LF_envp : z_envp usp argv = usp + 16 + 8 * Z.of_nat (length argv).
Proof. pose proof LF as H. tauto. Qed.
Let LF_auxv : z_auxv usp argv envp = z_envp usp argv + 8 * Z.of_nat (length envp) + 8.
Proof. pose proof LF as H. tauto. Qed.
Let LF_rand : z_rand usp krs argv envp
= z_auxv usp argv envp + AUXV_BYTES krs + 8 * Z.of_nat (block_items argv envp mod 2).
Proof. pose proof LF as H. tauto. Qed.
(* THE ORDER FLIPPED.  Pre-revision the strings block sat BELOW the random block
   ([z_strs <= z < z_rand] was the covered range).  At 75d69e00 [z_strs] counts DOWN from
   [ztop], and [layout_facts]'s fourth conjunct (YP08.v:756) puts the random block BELOW the
   strings: [z_rand + 16 <= z_strs].  Every range in this file that was written
   [z_strs .. z_rand] therefore has to become [z_strs .. ztop]. *)
Let LF_rand_strs : z_rand usp krs argv envp + 16 <= z_strs ztop argv envp efn.
Proof. pose proof LF as H. tauto. Qed.
Let LF_argv0 : z_argv ztop argv envp efn 0 = z_strs ztop argv envp efn.
Proof. pose proof LF as H. tauto. Qed.
Let LF_sum : z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv)
+ Z.of_nat (total_arg_bytes_nat envp) + Z.of_nat (length efn) + 1 + 8 = ztop.
Proof. pose proof LF as H. tauto. Qed.
Let LF_top : ztop <= SP_HI.
Proof. pose proof LF as H. tauto. Qed.
Let LF_sp : SP_LO <= usp <= SP_HI.
Proof. pose proof LF as H. tauto. Qed.
(* [z_rand + 16 < 2^63] is no longer a conjunct of [layout_facts]; its surviving form is
   [YP08.z_rand_end] (YP08.v:695). *)
Let LF_rand_end : z_rand usp krs argv envp + 16 < 2 ^ 63.
Proof. exact (YP08.z_rand_end TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau). Qed.
(* The strings block runs UP from [z_strs] to [ztop]: [YP08.stack_tail_end] (YP08.v:633). *)
Let LF_tail_end : z_strs ztop argv envp efn + Z.of_nat (length (stack_tail argv envp efn)) = ztop.
Proof. exact (YP08.stack_tail_end TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau). Qed.
Lemma uS0 : u eSp0 = usp.
Proof.
pose proof (SINV_sp0 E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as X.
rewrite eSp0_e_sp0. unfold YA02.TOP in X. lia.
Qed.
#[local] Notation V n := (bv_unsigned (ev E n)).
Lemma ev0 : V 0 = usp / 32768.
Proof.
rewrite (HE 0%nat) by (unfold NX0G; lia). cbn. pose proof (proj1 Hsp) as L. pose proof (proj1 (proj2 Hsp)) as Hh.
unfold sp_window_lo in L. unfold sp_window_hi in Hh. apply u64_lit. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma ev6 : V 6 = (usp mod 32768) / 16.
Proof.
rewrite (HE 6%nat) by (unfold NX0G; lia). cbn. apply u64_lit. pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)).
split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma uSp0 : u eSp0 = 32768 * V 0 + 16 * V 6 /\ 140735340871680 <= u eSp0 <= 140737488355328.
Proof.
pose proof uS0 as U. pose proof ev0 as E0'. pose proof ev6 as E6'. pose proof Hsp as (L & Hh & M16).
unfold sp_window_lo in L. unfold sp_window_hi in Hh.
pose proof (Z.div_mod usp 32768 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound usp 32768 ltac:(lia)) as D2.
pose proof (Z.div_mod (usp mod 32768) 16 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound (usp mod 32768) 16 ltac:(lia)) as D4.
pose proof (Z.div_mod usp 16 ltac:(lia)) as D5.
assert (A : usp = 32768 * (usp / 32768) + 16 * ((usp mod 32768) / 16)) by lia.
rewrite U, E0', E6'. split; [exact A | lia].
Qed.
Lemma uB5 : u B5 = usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp).
Proof.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0.
pose proof ev1 as V1. pose proof ev2 as V2. pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. pose proof (uE_bound E eSp0) as BS. rewrite uE_var in B0, B6.
unfold uE in V1, V2.
assert (M0 : u (EMd M_MUL (ELit 32768) (EVar 0)) = 32768 * bv_unsigned (ev E 0)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M6 : u (EMd M_MUL (ELit 16) (EVar 6)) = 16 * bv_unsigned (ev E 6)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M1 : u (EMd M_MUL (ELit 8) (EVar 1)) = 8 * Z.of_nat (length argv)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M2 : u (EMd M_MUL (ELit 8) (EVar 2)) = 8 * Z.of_nat (length envp)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (A3 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))) = 8 * Z.of_nat (length envp) + 16 * bv_unsigned (ev E 6))
by (rewrite uE_add; rewrite M2, M6; lia).
assert (A2 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EMd M_MUL (ELit 16) (EVar 6))))
= 8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + 16 * bv_unsigned (ev E 6)))
by (rewrite uE_add; rewrite M1, A3; lia).
unfold B5. rewrite uE_add; rewrite M0, A2; lia.
Qed.
Lemma uBR : u BR + (HEAD RZ - 16) = z_rand usp krs argv envp.
Proof.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0.
pose proof ev1 as V1. pose proof ev2 as V2. pose proof ev9 as V9. pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. rewrite uE_var in B0, B6.
pose proof (YP08.yp_gap_range argv envp) as HG. pose proof (YP08.rand_off_eq krs argv envp) as HRO. pose proof (YP08.items_eq argv envp) as HI.
pose proof (auxv_bytes_rz krs) as HA.
unfold uE in V1, V2.
assert (M0 : u (EMd M_MUL (ELit 32768) (EVar 0)) = 32768 * bv_unsigned (ev E 0)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M6 : u (EMd M_MUL (ELit 16) (EVar 6)) = 16 * bv_unsigned (ev E 6)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M1 : u (EMd M_MUL (ELit 8) (EVar 1)) = 8 * Z.of_nat (length argv)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M2 : u (EMd M_MUL (ELit 8) (EVar 2)) = 8 * Z.of_nat (length envp)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M9 : u (EMd M_MUL (ELit 8) (EVar 9)) = 8 * bv_unsigned (ev E 9)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (A4 : u (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))) = 16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9))
by (rewrite uE_add; rewrite M6, M9; lia).
assert (A3 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))
= 8 * Z.of_nat (length envp) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9))) by (rewrite uE_add; rewrite M2, A4; lia).
assert (A2 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9)))))
= 8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9)))) by (rewrite uE_add; rewrite M1, A3; lia).
unfold BR. rewrite uE_add; rewrite M0, A2; [|lia]. unfold z_rand, HEAD. lia.
Qed.
(* [BS] is [sp + 8 argc + 8 envc + V_W + 8 V_G]; with [HEAD] it is argv[0]'s first byte,
   [StackLayout]'s [sp + block_head_size + block_pad_len] (YP08.yp_pad_eq, YP08.head_eq). *)
Lemma uBS : u BS = usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + V 4 + 8 * V 9.
Proof.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0.
pose proof ev1 as V1. pose proof ev2 as V2. pose proof ev4 as V4. pose proof ev9 as V9.
pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
pose proof (YP08.yp_pad_eq TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as HP.
pose proof (YP08.top_le TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as HT.
pose proof (Nat2Z.is_nonneg (block_head_size krs argv envp)).
pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp efn)).
pose proof (Nat2Z.is_nonneg (block_pad_len krs sp (ed_top rdraw) argv envp efn)).
pose proof (YP08.yp_gap_range argv envp) as HG.
pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. rewrite uE_var in B0, B6.
unfold SP_HI in HT. unfold uE in V1, V2.
assert (M0 : u (EMd M_MUL (ELit 32768) (EVar 0)) = 32768 * bv_unsigned (ev E 0)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M6 : u (EMd M_MUL (ELit 16) (EVar 6)) = 16 * bv_unsigned (ev E 6)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M1 : u (EMd M_MUL (ELit 8) (EVar 1)) = 8 * Z.of_nat (length argv)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M2 : u (EMd M_MUL (ELit 8) (EVar 2)) = 8 * Z.of_nat (length envp)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M9 : u (EMd M_MUL (ELit 8) (EVar 9)) = 8 * bv_unsigned (ev E 9)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (A5 : u (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))) = 16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9))
by (rewrite uE_add; rewrite M6, M9; lia).
assert (A4 : u (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))
= bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9)))
by (rewrite uE_add; rewrite ?uE_var, A5; lia).
assert (A3 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9)))))
= 8 * Z.of_nat (length envp) + (bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9))))
by (rewrite uE_add; rewrite M2, A4; lia).
assert (A2 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))))
= 8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9)))))
by (rewrite uE_add; rewrite M1, A3; lia).
unfold BS. rewrite uE_add; rewrite M0, A2; lia.
Qed.
Lemma uBS_head : u BS + HEAD RZ = z_strs ztop argv envp efn.
Proof.
pose proof uBS as HB. pose proof ev4 as V4. pose proof ev9 as V9.
pose proof (YP08.yp_pad_eq TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as HP.
pose proof (YP08.head_eq krs argv envp) as HH. pose proof (YP08.items_eq argv envp) as HI.
pose proof (auxv_bytes_rz krs) as HA.
unfold z_strs, HEAD. lia.
Qed.
Lemma u_BS_head : u (EAlu ALU_ADD BS (ELit (HEAD RZ))) = z_argv ztop argv envp efn 0.
Proof.
pose proof uBS_head as H0. pose proof LF_argv0 as L4. pose proof LF_sum as L5. pose proof LF_top as L6.
pose proof (uE_bound E BS) as BB. pose proof (rseq_z_range krs) as HR.
pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat argv)). pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat envp)).
pose proof (Nat2Z.is_nonneg (length efn)).
unfold SP_HI in L6.
rewrite uE_add; rewrite ?uE_litv; unfold HEAD in *; lia.
Qed.
Lemma u_B5_24 : u (EAlu ALU_ADD B5 (ELit 24)) = z_auxv usp argv envp.
Proof.
pose proof uB5 as HB. pose proof LF_envp. pose proof LF_auxv. pose proof LF_rand.
pose proof LF_rand_strs. pose proof LF_argv0. pose proof LF_sp as L7. unfold SP_LO, SP_HI in L7.
(* the no-wrap side condition of [uE_add]: [z_rand + 16 < 2^63] ([LF_rand_end]) with the auxv's
   size [AUXV_BYTES krs >= 432] *)
pose proof LF_rand_end. pose proof (auxv_bytes_rz krs). pose proof (rseq_z_range krs).
pose proof (Nat2Z.is_nonneg (block_items argv envp mod 2)).
rewrite uE_add; rewrite ?uE_litv; lia.
Qed.
Lemma uE_mul : forall a b, u a * u b < 2 ^ 64 -> u (EMd M_MUL a b) = u a * u b.
Proof.
intros a b Hab. pose proof (uE_bound E a). pose proof (uE_bound E b). pose proof (uE_bound E (EMd M_MUL a b)).
assert (M : eqm (u (EMd M_MUL a b)) (u a * u b)) by (unfold uE; cbn [edenot]; apply u_mul_eqm).
destruct M as [q Hq]. assert (q = 0) by nia. subst q. lia.
Qed.
Lemma uE_sltu : forall a b, u (EAlu ALU_SLTU a b) = if u a <? u b then 1 else 0.
Proof. intros a b. unfold uE. cbn [edenot]. apply u_sltu64. Qed.
Lemma u_eArgv1 : (2 <= length argv)%nat -> u (eArgv1 RZ) = z_argv ztop argv envp efn 1.
Proof.
intros H2. pose proof uBS_head as H0. pose proof uBS as HB.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0.
pose proof ev1 as V1. pose proof ev2 as V2. pose proof ev3 as V3. pose proof ev4 as V4. pose proof ev9 as V9.
pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
pose proof LF_argv0 as L4. pose proof LF_sum as L5. pose proof LF_top as L6. unfold SP_HI in L6.
pose proof (uE_bound E BS) as BB. pose proof (rseq_z_range krs) as HR. pose proof (YP08.yp_gap_range argv envp) as HG.
pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat argv)). pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat envp)).
pose proof (Nat2Z.is_nonneg (length efn)).
assert (Z0 : z_argv ztop argv envp efn 0 + Z.of_nat (length (nth 0 argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (apply (YP08.z_argv_end TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 0); lia).
pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. pose proof (uE_bound E (EVar 3)) as B3.
pose proof (uE_bound E (EVar 4)) as B4. rewrite uE_var in B0, B6, B3, B4.
unfold uE in V1, V2, V3.
(* the no-wrap side conditions of the [uE_add] chain below (A6 .. A1): every summand is bounded by the
   stack's top [ztop <= SP_HI]: argv[0]'s length through [Z0], [LF_argv0] and [LF_sum], the pad and the gap
   through [uBS] and [uBS_head] with [HEAD RZ >= 0], and [z_strs >= 0] through the layout's lower chain *)
pose proof LF_envp. pose proof LF_auxv. pose proof LF_rand. pose proof LF_rand_strs.
pose proof LF_sp as L7. unfold SP_LO, SP_HI in L7.
pose proof (auxv_bytes_rz krs). pose proof (Nat2Z.is_nonneg (block_items argv envp mod 2)).
assert (HH : 0 <= HEAD RZ) by (unfold HEAD; lia).
assert (HS : u (EAlu ALU_SLTU (ELit 1) (EVar 1)) = 1).
{ rewrite uE_sltu, uE_litv, uE_var, V1 by lia.
destruct (1 <? Z.of_nat (length argv)) eqn:Hl; [reflexivity | apply Z.ltb_ge in Hl; lia]. }
assert (M0 : u (EMd M_MUL (ELit 32768) (EVar 0)) = 32768 * bv_unsigned (ev E 0)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M6 : u (EMd M_MUL (ELit 16) (EVar 6)) = 16 * bv_unsigned (ev E 6)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M1 : u (EMd M_MUL (ELit 8) (EVar 1)) = 8 * Z.of_nat (length argv)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M2 : u (EMd M_MUL (ELit 8) (EVar 2)) = 8 * Z.of_nat (length envp)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M9 : u (EMd M_MUL (ELit 8) (EVar 9)) = 8 * bv_unsigned (ev E 9)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (A6 : u (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))) = 16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9))
by (rewrite uE_add; rewrite M6, M9; lia).
assert (A5 : u (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))
= bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9)))
by (rewrite uE_add; rewrite ?uE_var, A6; lia).
assert (A4 : u (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9)))))
= bv_unsigned (ev E 3) + (bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9))))
by (rewrite uE_add; rewrite ?uE_var, A5; lia).
assert (A3 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))))
= 8 * Z.of_nat (length envp) + (bv_unsigned (ev E 3) + (bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9)))))
by (rewrite uE_add; rewrite M2, A4; lia).
assert (A2 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9)))))))
= 8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (bv_unsigned (ev E 3) + (bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9))))))
by (rewrite uE_add; rewrite M1, A3; lia).
assert (A1 : u (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))))))
= 32768 * bv_unsigned (ev E 0) + (8 * Z.of_nat (length argv) + (8 * Z.of_nat (length envp) + (bv_unsigned (ev E 3) + (bv_unsigned (ev E 4) + (16 * bv_unsigned (ev E 6) + 8 * bv_unsigned (ev E 9)))))))
by (rewrite uE_add; rewrite M0, A2; lia).
assert (HI : u (EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 2)) (EAlu ALU_ADD (EVar 3) (EAlu ALU_ADD (EVar 4) (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 6)) (EMd M_MUL (ELit 8) (EVar 9))))))))
(ELit (HEAD RZ + 1))) = u BS + Z.of_nat (length (nth 0 argv [])) + HEAD RZ + 1).
{ rewrite uE_add; rewrite ?A1, ?uE_litv; unfold HEAD in *; lia. }
unfold eArgv1. cbv beta. rewrite uE_mul by (rewrite HS, HI; lia). rewrite HS, HI, Z.mul_1_l.
rewrite (z_argv1_eq ztop argv envp efn ltac:(lia)). lia.
Qed.
Lemma u_eEnvp : u eEnvp = z_envp usp argv.
Proof.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0. pose proof ev1 as V1.
pose proof (proj1 Hva). pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. rewrite uE_var in B0, B6. unfold uE in V1.
pose proof LF_envp as L1. pose proof LF_sp as L7. unfold SP_LO, SP_HI in L7.
assert (M0 : u (EMd M_MUL (ELit 32768) (EVar 0)) = 32768 * bv_unsigned (ev E 0)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M6 : u (EMd M_MUL (ELit 16) (EVar 6)) = 16 * bv_unsigned (ev E 6)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (M1 : u (EMd M_MUL (ELit 8) (EVar 1)) = 8 * Z.of_nat (length argv)) by (rewrite uE_mul_lit; rewrite ?uE_var; lia).
assert (A2 : u (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EMd M_MUL (ELit 16) (EVar 6))) = 8 * Z.of_nat (length argv) + 16 * bv_unsigned (ev E 6))
by (rewrite uE_add; rewrite M1, M6; lia).
assert (A1 : u (EAlu ALU_ADD (EMd M_MUL (ELit 32768) (EVar 0)) (EAlu ALU_ADD (EMd M_MUL (ELit 8) (EVar 1)) (EMd M_MUL (ELit 16) (EVar 6))))
= 32768 * bv_unsigned (ev E 0) + (8 * Z.of_nat (length argv) + 16 * bv_unsigned (ev E 6))) by (rewrite uE_add; rewrite M0, A2; lia).
unfold eEnvp. rewrite uE_add; rewrite A1, ?uE_litv; lia.
Qed.
Lemma spellings_sound : forall ob rb d, In (rb, d) (spellings RZ ob) -> base_val EL ob = u rb + d.
Proof.
intros ob rb d Hin. destruct ob as [[|[|[|[|[|[|[|n]]]]]]]|]; cbn [spellings] in Hin; try (cbn in Hin; contradiction).
- destruct Hin as [Hin|[]]. injection Hin as <- <-. cbn [base_val]. rewrite EL0, uS0. lia.
- destruct Hin as [Hin|[]]. injection Hin as <- <-. cbn [base_val]. pose proof LF_envp. pose proof LF_auxv. rewrite EL5, uB5. lia.
- destruct Hin as [Hin|[]]. injection Hin as <- <-. cbn [base_val]. rewrite EL6. pose proof uBR. lia.
- destruct Hin as [Hin|[]]. injection Hin as <- <-. cbn [base_val]. rewrite uE_litv by lia. reflexivity.
Qed.
Lemma edenot_uE : forall e, edenot E e = Z_to_bv 64 (u e).
Proof. intros e. unfold uE. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
Definition two_ok (two : bool) : Prop := if two then (2 <= List.length (in_argv inp))%nat else True.
Lemma VT_sound : forall (two : bool) v s, two_ok two -> In (v, s) (VT two RZ) -> sv_denot EL s = edenot E v.
Proof.
intros two v s Htwo Hin. unfold VT in Hin. apply in_app_iff in Hin as [Hin|Hin].
- destruct Hin as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|[]]]]]]]]]]]; injection H as <- <-; cbn [sv_denot]; rewrite ?Z.add_0_r.
+ rewrite EL3, <- ev1. apply Z_to_bv_bv_unsigned.
+ rewrite EL8. apply Z_to_bv_bv_unsigned.
+ rewrite EL8. cbn [edenot]. apply bv_eq. pose proof (u_ext_zx 0 4 (ev E TIDV)) as (X & _ & _). rewrite X.
pose proof tid_range. rewrite u64_lit by lia. change (2 ^ (8 * Z.of_nat 0)) with 1. change (2 ^ (8 * Z.of_nat 4)) with 4294967296.
rewrite Z.div_1_r, Z.mod_small by lia. reflexivity.
+ rewrite EL1, edenot_uE, u_BS_head. rewrite LF_argv0. reflexivity.
+ rewrite EL5, edenot_uE, u_B5_24. reflexivity.
+ change (edenot E (EVar 8)) with (ev E 8). rewrite ev8. unfold data_word. cbn [ed EL YP08.E0 xdE Nat.eqb UID_DATOM N.to_nat Z.to_nat skipn].
unfold uid_bytes. change (firstn (N.to_nat 8) (skipn (Z.to_nat 0) (word_le8 (in_uid inp)))) with (word_le8 (in_uid inp)).
rewrite bytes_le_n_to_le_8. apply Z_to_bv_bv_unsigned.
+   rewrite EL41. apply Z_to_bv_bv_unsigned.
+ rewrite EL0, edenot_uE. f_equal. pose proof uS0 as U0. pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
rewrite uE_add_neglit; lia.
+ rewrite EL0, edenot_uE. f_equal. pose proof uS0 as U0. pose proof (proj1 (proj2 Hsp)) as L. unfold sp_window_hi in L.
rewrite uE_add; rewrite ?uE_litv; lia.
+ rewrite EL4, edenot_uE. f_equal. symmetry. exact u_eEnvp.
- destruct two; [|destruct Hin]. destruct Hin as [H|[]]. injection H as <- <-. cbn [sv_denot]. rewrite Z.add_0_r. unfold two_ok in Htwo.
rewrite (EL2 Htwo), edenot_uE, (u_eArgv1 Htwo). reflexivity.
Qed.
Lemma vmatch_sound : forall (two : bool) v s, two_ok two -> vmatch two RZ v s = true -> sv_denot EL s = edenot E v.
Proof.
intros two v s Htwo H.
assert (GEN : existsb (fun p => expr_eqb (fst p) v && sv_eqb (snd p) s)%bool (VT two RZ) = true -> sv_denot EL s = edenot E v).
{ intros Hx. apply existsb_exists in Hx as ([v' s'] & Hin & Heq). cbn [fst snd] in Heq. apply andb_prop in Heq as [H1 H2].
apply expr_eqb_eq in H1. apply sv_eqb_eq in H2. subst v' s'. exact (VT_sound two v s Htwo Hin). }
destruct v; try (apply GEN; exact H). destruct s; try (apply GEN; exact H).
cbn [vmatch] in H. apply Z.eqb_eq in H. subst. reflexivity.
Qed.
Let Hbyte := ho_read_byte TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Let Hbound := ho_read_bound TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Let Hzc := ho_zcover_range TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC TFIB_BSS tfib_bss_rom.
Let Himg := ho_img_at TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Lemma hreader_mbyte : forall a z, hreader TSEGS MR a = Some z -> exists b : byte, mbyte TSEGS MR a = Some b /\ bv_unsigned b = z.
Proof.
intros a z H. unfold hreader in H. destruct (mbyte TSEGS MR a) as [b|]; [|discriminate H]. cbn in H. injection H as <-.
exists b. split; reflexivity.
Qed.
Lemma cjust_sound : forall (two : bool) ob c, two_ok two ->
cjust two RZ ch ob c = true -> chunk_ok TSEGS EL MR (base_val EL ob) c.
Proof.
intros two ob [off cv] Htwo H. unfold cjust in H. apply existsb_exists in H as ([rb d] & Hspl & H).
pose proof (spellings_sound ob rb d Hspl) as HB. cbn [YP09.c_val YP09.c_off] in H.
intros i Hi. unfold YP09.c_len in Hi. cbn [YP09.c_off YP09.c_val] in Hi |- *.
destruct cv as [w sv0|l|l|dd ss ll]; cbn [YP09.cv_len] in Hi; try discriminate H.
-
apply andb_prop in H as [Hw H]. destruct (kn_read TSEGS ch rb (off + d) (N.to_nat w)) as [v|] eqn:Hr; [|discriminate H].
pose proof (vmatch_sound two v sv0 Htwo H) as Hv. pose proof (N_nat_Z w) as HwN.
pose proof (Hbyte rb (off + d) (N.to_nat w) v Hr (Z.to_nat i) ltac:(lia)) as X.
replace (u rb + (off + d) + Z.of_nat (Z.to_nat i)) with (base_val EL ob + off + i) in X by lia.
destruct (hreader_mbyte _ _ X) as (b & Hmb & Hbu).
exists b. split; [|exact Hmb]. cbn [cbyte]. f_equal. unfold byte_of_word. apply bv_eq.
rewrite Z_to_bv_unsigned. rewrite Hbu. rewrite Hv. fold (u v). rewrite Z.shiftr_div_pow2 by lia.
rewrite Z2Nat.id by lia. unfold bv_wrap. change (bv_modulus 8) with 256. reflexivity.
-
pose proof (Hzc rb (off + d) l H i Hi) as X.
replace (u rb + (off + d) + i) with (base_val EL ob + off + i) in X by lia.
destruct (hreader_mbyte _ _ X) as (b & Hmb & Hbu).
exists b. split; [|exact Hmb]. cbn [cbyte]. f_equal. apply bv_eq. rewrite Hbu. reflexivity.
-
destruct ob as [n|]; [discriminate H|]. cbn [base_val] in *.
apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.leb_le in H4.
unfold kn_img in H1. apply existsb_exists in H1 as (K & HK & HKb). destruct K as [| | |lo hi| | | | | |]; try discriminate HKb.
apply andb_prop in HKb as [K1 K2]. apply Z.leb_le in K1. apply Z.leb_le in K2.
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ HK) as (_ & _ & Hnone).
pose proof (Hnone (off + i) ltac:(lia)) as X.
cbn [cbyte]. unfold img_byte, mbyte. rewrite Z.add_0_l. rewrite X.
destruct (seg_rom TSEGS (Z_to_bv 64 (off + i))) as [b|] eqn:Hs; [exists b; split; reflexivity|].
exfalso. exact (tfib_rom_all (off + i) ltac:(lia) Hs).
Qed.
Lemma store_ok1_wview : forall m (a : word), RiscvSemantics.store_ok TSEGS m a 1 = true -> wview TSEGS m a <> None.
Proof. intros m a H. cbn [RiscvSemantics.store_ok] in H. destruct (wview TSEGS m a); [discriminate | discriminate H]. Qed.
Lemma wjust_sound : forall r, wjust ch r = true ->
forall o, r_wlo r <= o < r_whi r -> writable_at TSEGS MR (base_val EL (r_base r) + o).
Proof.
intros r H o Ho. unfold wjust in H. apply orb_prop in H as [H|H]; [apply Z.leb_le in H; lia|].
destruct (r_base r) as [[|n]|].
- apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H2. apply Z.leb_le in H3.
cbn [base_val]. rewrite EL0. unfold writable_at.
pose proof (ho_wr TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ H1 (o + WDEPTH) 1%nat ltac:(unfold WDEPTH in *; lia)) as W.
unfold elenZ in W. cbn [edenot] in W. rewrite u64_lit in W by (unfold WDEPTH; lia). specialize (W ltac:(unfold WDEPTH in *; lia)).
unfold estart in W. cbn [a_base a_off] in W. fold (u eSp0) in W. rewrite uS0 in W.
replace (usp + - WDEPTH + (o + WDEPTH)) with (usp + o) in W by lia. exact (store_ok1_wview _ _ W).
- discriminate H.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [base_val].
unfold writable_at. apply tfib_rw_window. rewrite u64_lit by lia. lia.
Qed.
Lemma rjust_sound : forall two r, two_ok two -> rjust two RZ ch r = true -> region_ok TSEGS EL MR r.
Proof.
intros two r Htwo H. unfold rjust in H. apply andb_prop in H as [H HB]. apply andb_prop in H as [HC0 HW].
pose proof LF_envp. pose proof LF_auxv. pose proof LF_rand. pose proof LF_rand_strs.
pose proof LF_argv0. pose proof LF_sum. pose proof LF_top. pose proof LF_sp as L7.
unfold SP_LO, SP_HI in L7.
(* base 6 is [z_rand] ([EL6]).  Its bounds are proved, no premise added: above, [LF_rand_end] is
   Reusable/YP08.v's Lemma [z_rand_end] (YP08.v:692, from the stack layout: z_rand_strs, str_bounds,
   top_le) through this section's entry hypotheses; below, [AUXV_BYTES krs = 432 + 32 * rseq_z krs] is
   [auxv_bytes_rz] (vm_compute of AUXV_BYTES, this file) and [0 <= rseq_z krs <= 1] is Reusable/YK09.v's
   [rseq_z_range] (YK09.v:2288). *)
pose proof LF_rand_end. pose proof (auxv_bytes_rz krs). pose proof (rseq_z_range krs).
assert (BND : 0 <= base_val EL (r_base r) + r_lo r /\ base_val EL (r_base r) + r_hi r <= 2 ^ 64).
{ destruct (r_base r) as [[|[|[|[|[|[|[|n]]]]]]]|]; try discriminate HB; apply andb_prop in HB as [B1 B2]; apply Z.leb_le in B1; apply Z.leb_le in B2;
cbn [base_val]; [rewrite EL0; lia | rewrite EL6; lia | lia]. }
unfold region_ok. split; [exact (proj1 BND)|]. split; [exact (proj2 BND)|]. split.
- exact (wjust_sound r HW).
- apply Forall_forall. intros c Hc. apply (cjust_sound two); [exact Htwo|]. exact (proj1 (forallb_forall _ _) HC0 c Hc).
Qed.
Lemma img_stk_check : forall two, forallb (rjust two RZ ch) (R_stk :: IMG_REGIONS) = true.
Proof.
intros two. pose proof (proj1 (proj2 (CHK_parts two))) as H. cbn [forallb] in H |- *.
apply andb_prop in H as [H1 H]. apply andb_prop in H as [_ H3]. rewrite H1, H3. reflexivity.
Qed.
Definition H1 : word -> bool := fun a => (HID a && negb (argH E a) && negb (sliverb sp a))%bool.
#[local] Notation m1 := (mrestrict H1 FULL).
(* The SAME term as YP08's own [m0] abbreviation (YP08.v:507), so the [m0_*] lemmas below
   land on it without a conversion step: [wrap_mem] takes the whole [ProcInput] now. *)
#[local] Notation m0 := (wrap_mem inp mbase TPH entryw sp rdraw).
Lemma H1_sub : hsub H1 HID.
Proof. intros a Ha. unfold H1 in Ha. apply andb_prop in Ha as [Ha _]. apply andb_prop in Ha as [Ha _]. exact Ha. Qed.
Lemma MR_m1 : forall a b, MR a = Some b -> m1 a = Some b.
Proof.
intros a b H. rewrite Mr_is_mrestrict in H. unfold mrestrict, H1 in *.
destruct (hid TFIB TOP argH E ch model a); [discriminate H|]. cbn. exact H.
Qed.
Lemma mbyte_MR_m1 : forall a b, mbyte TSEGS MR a = Some b -> mbyte TSEGS m1 a = Some b.
Proof.
intros a b H. unfold mbyte in *. destruct (MR (Z_to_bv 64 a)) as [b'|] eqn:E1.
- rewrite (MR_m1 _ _ E1). exact H.
- rewrite Mr_is_mrestrict in E1. unfold mrestrict in E1. unfold mrestrict, H1.
destruct (hid TFIB TOP argH E ch model (Z_to_bv 64 a)) eqn:Eh.
+
exfalso. pose proof (ho_hid_off TSEGS TFIB TOP argH tfib_in_hull TOPok tfib_hull_ok ARGH E ch model _ Eh) as Hoff.
rewrite (seg_rom_none_of_find TSEGS _ Hoff) in H. discriminate H.
+ cbn. rewrite E1. exact H.
Qed.
Lemma wview_MR_m1 : forall a, wview TSEGS MR a <> None -> wview TSEGS m1 a <> None.
Proof.
intros a H. unfold wview in *. destruct (MR a) as [b|] eqn:E1.
- rewrite (MR_m1 _ _ E1). discriminate.
- rewrite Mr_is_mrestrict in E1. unfold mrestrict in E1. unfold mrestrict, H1.
destruct (hid TFIB TOP argH E ch model a) eqn:Eh.
+ exfalso. pose proof (ho_hid_off TSEGS TFIB TOP argH tfib_in_hull TOPok tfib_hull_ok ARGH E ch model _ Eh) as Hoff.
rewrite Hoff in H. exact (H eq_refl).
+ cbn. rewrite E1. exact H.
Qed.
Lemma region_ok_MR_m1 : forall r, region_ok TSEGS EL MR r -> region_ok TSEGS EL m1 r.
Proof.
intros r (A1 & A2 & A3 & A4). split; [exact A1|]. split; [exact A2|]. split.
- intros o Ho. unfold writable_at. apply wview_MR_m1. exact (A3 o Ho).
- apply Forall_impl with (2 := A4). intros c Hc i Hi. destruct (Hc i Hi) as (b & Hb1 & Hb2).
exists b. split; [exact Hb1 | exact (mbyte_MR_m1 _ _ Hb2)].
Qed.
Lemma m1_pristine : forall a : word, argH E a = true -> m1 a = m0 a.
Proof. intros a Ha. unfold mrestrict, H1. rewrite Ha. cbn. rewrite andb_false_r. cbn. exact (HM a Ha). Qed.
(* THE RANGE FLIPPED WITH THE ANCHOR.  Pre-revision the strings block was [z_strs .. z_rand]
   (strings below the random block, both counted up from sp).  At 75d69e00 [z_strs] counts
   DOWN from [ztop] and [layout_facts] conjunct 4 (YP08.v:756) puts the random block BELOW
   the strings, so the strings block is [z_strs .. ztop]; its upper end is
   [YP08.stack_tail_end] (YP08.v:633), named [LF_tail_end] above. *)
Lemma argH_range2 : forall z, z_strs ztop argv envp efn <= z < ztop -> argH E (Z_to_bv 64 z) = true.
Proof.
intros z Hz.
pose proof (YP08.yp_pad_eq TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as HP.
pose proof (YP08.str_bounds TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau) as [HSlo _].
pose proof LF_top as HT. unfold SP_HI in HT. pose proof (u64_range sp).
assert (HS : usp + Z.of_nat (YK0h.cat_string_off krs sp (ed_top rdraw) argv envp efn)
= z_strs ztop argv envp efn).
{ unfold YK0h.cat_string_off. rewrite Nat2Z.inj_add. unfold z_strs. lia. }
unfold YA02.argH0. cbn beta. rewrite u64_lit by lia.
apply orb_true_iff. right.
change (((usp + Z.of_nat (YK0h.cat_string_off krs sp (ed_top rdraw) argv envp efn) <=? z)
&& (z <? ztop))%bool = true).
rewrite HS. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.
Lemma argH_range1 : forall z, z_envp usp argv <= z < z_auxv usp argv envp -> argH E (Z_to_bv 64 z) = true.
Proof.
intros z Hz. pose proof LF_envp. pose proof LF_auxv. pose proof LF_rand.
pose proof LF_rand_strs. pose proof LF_sp as L7. unfold SP_LO, SP_HI in L7.
pose proof (proj1 Hva). pose proof (proj1 Hve).
unfold argH0. cbn beta. rewrite u64_lit by lia.
apply orb_true_iff. left. apply andb_true_iff. split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.
Lemma bytes_at_m1 : forall a bs, YP08.bytes_at m0 a bs -> (forall j, (j < length bs)%nat -> argH E (Z_to_bv 64 (a + Z.of_nat j)) = true) ->
YP03.bytes_at m1 a bs.
Proof. intros a bs H HA j Hj. rewrite (m1_pristine _ (HA j Hj)). exact (H j Hj). Qed.
Lemma region_ok_pristine : forall r, region_ok TSEGS EL m0 r -> r_whi r <= r_wlo r ->
(forall a, base_val EL (r_base r) + r_lo r <= a < base_val EL (r_base r) + r_hi r -> argH E (Z_to_bv 64 a) = true) ->
forallb (chunk_inside r) (r_chunks r) = true ->
region_ok TSEGS EL m1 r.
Proof.
intros r (A1 & A2 & A3 & A4) Hw HA Hci. split; [exact A1|]. split; [exact A2|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (forallb_forall _ _) Hci c Hc) as Hin. unfold chunk_inside in Hin.
apply andb_prop in Hin as [Hin _]. apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.leb_le in I2.
destruct (proj1 (Forall_forall _ _) A4 c Hc i Hi) as (b & Hb1 & Hb2). exists b. split; [exact Hb1|].
unfold mbyte in *. rewrite (m1_pristine _ (HA (base_val EL (r_base r) + YP09.c_off c + i) ltac:(lia))). exact Hb2.
Qed.
Definition smem_main (two : bool) : smem :=
[R_stk; R_hdr two; R_argv0] ++ (if two then [R_argv1] else []) ++ IMG_REGIONS.
Lemma hdr_check : forall two, rjust two RZ ch (R_hdr two) = true.
Proof.
intros two. pose proof (proj1 (proj2 (CHK_parts two))) as H. cbn [forallb] in H.
apply andb_prop in H as [_ H]. apply andb_prop in H as [H2 _]. exact H2.
Qed.
Lemma smem_main_wf : forall two, regions_wf (smem_main two) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma region_ok_all : forall two, two_ok two -> Forall (region_ok TSEGS EL m1) (smem_main two).
Proof.
intros two Htwo. pose proof (img_stk_check two) as CK. cbn [forallb] in CK. apply andb_prop in CK as [CKs CKi].
pose proof (hdr_check two) as CKh.
pose proof LF_envp. pose proof LF_auxv. pose proof LF_rand. pose proof LF_rand_strs.
pose proof LF_argv0 as L4. pose proof LF_sum. pose proof LF_top. pose proof LF_sp as L7.
unfold SP_LO, SP_HI in L7.
unfold smem_main. apply Forall_app. split; [|apply Forall_app; split].
- constructor; [apply region_ok_MR_m1; exact (rjust_sound two _ Htwo CKs)|].
constructor; [apply region_ok_MR_m1; exact (rjust_sound two _ Htwo CKh)|].
constructor; [|constructor].
apply region_ok_pristine; [exact (YP08.region_ok_argv0 TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE xdE_uid xdE_hwcap xdE_rand xdE_gid xdE_ehdr xdE_execfn) | cbn; lia | | reflexivity].
cbn [r_base r_lo r_hi R_argv0 base_val]. rewrite EL1. intros a Ha. apply argH_range2.
assert (Z0 : z_argv ztop argv envp efn 0 + Z.of_nat (length (nth 0 argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (apply (YP08.z_argv_end TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 0); pose proof (proj1 Hva); lia).
pose proof LF_tail_end. pose proof LF_sum. rewrite L4 in Z0. lia.
- destruct two; [|constructor]. constructor; [|constructor]. unfold two_ok in Htwo.
apply region_ok_pristine; [exact (YP08.region_ok_argv1 TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE xdE_uid xdE_hwcap xdE_rand xdE_gid xdE_ehdr xdE_execfn Htwo) | cbn; lia | | reflexivity].
cbn [r_base r_lo r_hi R_argv1 base_val]. rewrite (EL2 Htwo). intros a Ha. apply argH_range2.
assert (Z1 : z_argv ztop argv envp efn 1 + Z.of_nat (length (nth 1 argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (apply (YP08.z_argv_end TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 1); lia).
assert (z_argv ztop argv envp efn 0 <= z_argv ztop argv envp efn 1)
by (unfold z_argv; cbn [firstn]; generalize Htwo; generalize (in_argv inp) as av;
intros av Hav; destruct av; cbn in *; lia).
pose proof LF_tail_end. pose proof LF_sum. lia.
- apply Forall_forall. intros r Hr. apply region_ok_MR_m1. apply (rjust_sound two _ Htwo). exact (proj1 (forallb_forall _ _) CKi r Hr).
Qed.
Definition ext_disj_abs (r1 r2 : YP09.region) : bool :=
match r_base r1, r_base r2 with
| None, None => (r_hi r1 <=? r_lo r2) || (r_hi r2 <=? r_lo r1)
| _, _ => false
end%bool.
Fixpoint all_disj_abs (r : YP09.region) (rs : smem) : bool :=
match rs with [] => true | r' :: rs' => ext_disj_abs r r' && all_disj_abs r rs' end%bool.
Fixpoint pd_abs (rs : smem) : bool :=
match rs with [] => true | r :: rs' => all_disj_abs r rs' && pd_abs rs' end%bool.
Lemma ext_disj_abs_sound : forall En r1 r2, ext_disj_abs r1 r2 = true -> extent_disjoint En r1 r2.
Proof.
intros En r1 r2 H. unfold ext_disj_abs in H. unfold extent_disjoint.
destruct (r_base r1) eqn:B1; [discriminate H|]. destruct (r_base r2) eqn:B2; [discriminate H|]. cbn [base_val].
apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.
Lemma all_disj_abs_sound : forall En r rs, all_disj_abs r rs = true -> all_disjoint En r rs.
Proof.
intros En r rs; induction rs as [|r' rs IH]; intros H; cbn in *; [exact I|].
apply andb_prop in H as [H1 H2]. split; [exact (ext_disj_abs_sound En r r' H1) | exact (IH H2)].
Qed.
Lemma pd_abs_sound : forall En rs, pd_abs rs = true -> pairwise_disjoint En rs.
Proof.
intros En rs; induction rs as [|r rs IH]; intros H; cbn in *; [exact I|].
apply andb_prop in H as [H1 H2]. split; [exact (all_disj_abs_sound En r rs H1) | exact (IH H2)].
Qed.
Lemma img_regions_pd : pd_abs IMG_REGIONS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_regions_abs : forallb (fun r => match r_base r with None => (0 <=? r_lo r) && (r_hi r <=? 0x5f9000) | _ => false end)%bool IMG_REGIONS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_region_shape : forall r, In r IMG_REGIONS -> r_base r = None /\ r_hi r <= 0x5f9000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) img_regions_abs r Hr) as H. cbn beta in H.
destruct (r_base r); [discriminate H|]. apply andb_prop in H as [_ H]. apply Z.leb_le in H. split; [reflexivity | exact H].
Qed.
Lemma smem_main_disjoint : forall two, two_ok two -> pairwise_disjoint EL (smem_main two).
Proof.
intros two Htwo.
pose proof LF_envp. pose proof LF_auxv. pose proof LF_rand. pose proof LF_rand_strs.
pose proof LF_argv0 as L5. pose proof LF_sum. pose proof LF_top. pose proof LF_tail_end.
pose proof LF_sp as L7. unfold SP_LO, SP_HI in L7.
pose proof (proj1 Hva) as HA. pose proof EL0 as E0'. pose proof EL1 as E1'. pose proof EL6 as E6'.
(* [z_rand]'s bounds, proved as in [rjust_sound]: YP08.z_rand_end (YP08.v:692), auxv_bytes_rz, YK09.rseq_z_range *)
pose proof LF_rand_end. pose proof (auxv_bytes_rz krs). pose proof (rseq_z_range krs).
assert (B0 : z_strs ztop argv envp efn <= z_argv ztop argv envp efn 0
/\ z_argv ztop argv envp efn 0 + Z.of_nat (length (nth 0 argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (apply (YP08.z_argv_bounds TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 0); lia).
destruct B0 as [B0a B0b].
(* The strings run UP to [ztop] now, not up to [z_rand]: the old upper end
   [z_argv 1 + 1 <= z_rand] is replaced by [z_argv 1 + 1 <= ztop]. *)
assert (TWO : forall r, In r (if two then [R_argv1] else []) ->
two = true /\ r = R_argv1 /\ bv_unsigned (ew EL 2) = z_argv ztop argv envp efn 1
/\ z_argv ztop argv envp efn 0 + 1 <= z_argv ztop argv envp efn 1
/\ z_argv ztop argv envp efn 1 + 1 <= ztop).
{ intros r Hr. destruct two; [|destruct Hr]. destruct Hr as [<-|[]]. unfold two_ok in Htwo.
assert (B1 : z_strs ztop argv envp efn <= z_argv ztop argv envp efn 1
/\ z_argv ztop argv envp efn 1 + Z.of_nat (length (nth 1 argv [])) + 1
<= z_strs ztop argv envp efn + Z.of_nat (total_arg_bytes_nat argv))
by (apply (YP08.z_argv_bounds TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 1); lia).
destruct B1 as [B1a B1b].
split; [reflexivity|]. split; [reflexivity|]. split; [exact (EL2 Htwo)|].
unfold z_argv in *. rewrite firstn_O in *. change (total_arg_bytes_nat []) with 0%nat in *.
(* the strings' end [ztop] through [LF_sum], taken over the same generalised argv as the bounds above *)
pose proof LF_sum as L6s.
revert Htwo B0a B0b B1a B1b L5 L6s. generalize (in_argv inp) as av. intros av Htwo B0a B0b B1a B1b L5 L6s.
destruct av as [|a0 [|a1 r]]; cbn in Htwo; try lia. cbn [firstn total_arg_bytes_nat fold_right nth] in *. cbn in B1b. lia. }
unfold smem_main.
apply YP08.pairwise_disjoint_app; [|apply YP08.pairwise_disjoint_app|].
-
cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
cbn [r_base r_lo r_hi R_stk R_hdr R_argv0 base_val WSTK]. rewrite !E0', !E1'.
destruct two; cbn [r_lo r_hi]; repeat split; first [left; lia | right; lia].
- destruct two; cbn; [split; exact I | exact I].
-
exact (pd_abs_sound EL IMG_REGIONS img_regions_pd).
- intros r1 r2 Hr1 Hr2. destruct (TWO r1 Hr1) as (-> & -> & E2' & F1 & F2).
unfold extent_disjoint. cbn [r_base r_lo r_hi R_argv1 base_val]. rewrite E2'.
destruct (img_region_shape r2 Hr2) as [Hb2 Hh2]. rewrite Hb2. cbn [base_val]. right. lia.
- intros r1 r2 Hr1 Hr2. apply in_app_iff in Hr2 as [Hr2|Hr2].
+ destruct (TWO r2 Hr2) as (-> & -> & E2' & F1 & F2). unfold extent_disjoint. cbn [r_base r_lo r_hi R_argv1 base_val]. rewrite E2'.
destruct Hr1 as [<-|[<-|[<-|[]]]]; cbn [r_base r_lo r_hi R_stk R_hdr R_argv0 base_val WSTK]; rewrite ?E0', ?E1'; cbn [r_lo r_hi]; lia.
+ destruct (img_region_shape r2 Hr2) as [Hb2 Hh2]. unfold extent_disjoint. rewrite Hb2.
destruct Hr1 as [<-|[<-|[<-|[]]]]; cbn [r_base r_lo r_hi R_stk R_hdr R_argv0 base_val WSTK]; rewrite ?E0', ?E1'; cbn [r_lo r_hi]; unfold WSTK; right; lia.
Qed.
Theorem mem_ok_main : forall two, two_ok two -> mem_ok TSEGS EL m1 (smem_main two).
Proof.
intros two Htwo. split; [apply smem_main_wf|]. split; [apply region_ok_all; exact Htwo | apply smem_main_disjoint; exact Htwo].
Qed.
Lemma bytes_at_app' : forall m a l1 l2,
YP03.bytes_at m a l1 -> YP03.bytes_at m (a + Z.of_nat (length l1)) l2 -> YP03.bytes_at m a (l1 ++ l2).
Proof.
intros m a l1 l2 B1 B2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl|Hg].
- rewrite nth_error_app1 by exact Hl. apply B1. exact Hl.
- rewrite nth_error_app2 by exact Hg.
replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. apply B2. lia.
Qed.
Lemma stack_strs_end : z_strs ztop argv envp efn
+ Z.of_nat (length (stack_strs argv envp (in_execfn inp))) = ztop - 8.
Proof.
pose proof LF_tail_end as B.
replace (stack_tail argv envp (in_execfn inp)) with (stack_strs argv envp (in_execfn inp) ++ repeat (Z_to_bv 8 0) 8) in B
by (unfold stack_tail, stack_strs; rewrite <- !app_assoc; reflexivity).
rewrite length_app, repeat_length in B. lia.
Qed.
Theorem runs_main_m1 : forall two, two_ok two -> runs_at usp m1 (runs_main_tfa two sp (ed_top rdraw) argv envp (in_execfn inp)).
Proof.
intros two Htwo.
pose proof LF_envp. pose proof LF_auxv. pose proof LF_rand. pose proof LF_rand_strs.
pose proof LF_argv0. pose proof LF_sum. pose proof LF_tail_end.
(* the entries' ends against 2^64: every entry ends at or below the stack VMA's end [ztop] (LF_sum,
   LF_tail_end), and [ztop <= SP_HI = 0x800000000000] is [LF_top] (YP08's layout facts), with SP_HI unfolded *)
pose proof LF_top as HTop. unfold SP_HI in HTop.
pose proof LF_sp as L7. unfold SP_LO, SP_HI in L7.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HEv.
(* [z_rand]'s bounds, proved as in [rjust_sound]: YP08.z_rand_end (YP08.v:692), auxv_bytes_rz, YK09.rseq_z_range *)
pose proof LF_rand_end. pose proof (auxv_bytes_rz krs). pose proof (rseq_z_range krs).
unfold runs_main_tfa. cbn [app]. apply Forall_cons; [|apply Forall_cons; [| apply Forall_app; split]].
- cbn [fst snd]. rewrite (length_envp_block (ed_top rdraw) argv envp efn).
split; [lia|]. split; [lia|]. unfold envp_block, envp_words. rewrite flat_map_app. apply bytes_at_app'.
+ apply bytes_at_m1; [exact (YP08.m0_envp_ptrs TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau)|].
rewrite length_flat_map_le8, length_string_addrs_fst. intros j Hj. apply argH_range1. lia.
+ rewrite length_flat_map_le8, length_string_addrs_fst. cbn [flat_map]. rewrite app_nil_r.
replace (z_envp usp argv + Z.of_nat (8 * length envp)) with (z_auxv usp argv envp - 8) by lia.
apply bytes_at_m1; [exact (YP08.m0_envp_null TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau)|].
rewrite length_n_to_le_8. intros j Hj. apply argH_range1. lia.
- cbn [fst snd].
pose proof (YP08.z_argv_bounds TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 0 ltac:(lia)) as [Ba Bb].
rewrite length_app. cbn [length]. split; [lia|]. split; [lia|].
apply bytes_at_m1; [apply (YP08.m0_argv_str TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 0); lia|].
rewrite length_app. cbn [length]. intros j Hj. apply argH_range2. lia.
- destruct two; [|constructor]. unfold two_ok in Htwo. apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (YP08.z_argv_bounds TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 1 Htwo) as [Ba Bb].
rewrite length_app. cbn [length]. split; [lia|]. split; [lia|].
apply bytes_at_m1; [apply (YP08.m0_argv_str TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau 1); lia|].
rewrite length_app. cbn [length]. intros j Hj. apply argH_range2. lia.
- apply Forall_cons; [|constructor]. cbn [fst snd].
split; [lia|]. split; [lia|].
apply bytes_at_m1; [exact (YP08.m0_tail TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau)|].
intros j Hj. apply argH_range2. lia.
Qed.
Lemma rcheck_all : forall two, forallb (rcheck two RZ ch) (seq 0 32) = true.
Proof. intros two. exact (proj1 (proj2 (proj2 (CHK_parts two)))). Qed.
Lemma regs_ok_main : forall two, two_ok two -> YP0l.regs_ok EL sregs_main R.
Proof.
intros two Htwo r. pose proof (rcheck_all two) as CK.
unfold YP0l.sr_get. destruct (bv_eqb r 0) eqn:Hr0.
{ unfold getr. rewrite Hr0. reflexivity. }
rewrite (ho_reg_idx TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC r Hr0). unfold APC.reg.
assert (Hi : (YP0l.ridx r < 32)%nat).
{ unfold YP0l.ridx. pose proof (bv_unsigned_in_range 5 r) as X. change (bv_modulus 5) with 32 in X. lia. }
assert (Hx : AX2.ridx r = YP0l.ridx r) by reflexivity. rewrite Hx.
pose proof (proj1 (forallb_forall _ _) CK (YP0l.ridx r) ltac:(apply in_seq; lia)) as C. unfold rcheck in C.
set (sv0 := nth (YP0l.ridx r) sregs_main (SLit 0)) in *. set (e0 := nth (YP0l.ridx r) (s_regs (a_ss ch)) (ELit 0)) in *.
apply orb_prop in C as [C|C].
- destruct sv0 as [|n z| | | | | | | | |]; try discriminate C. destruct z; try discriminate C. apply Nat.eqb_eq in C. subst n.
cbn [sv_denot]. rewrite Z.add_0_r, (ELF (9 + YP0l.ridx r)%nat) by lia.
replace (9 + YP0l.ridx r - 9)%nat with (YP0l.ridx r) by lia. unfold YP0l.ridx. rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range 5 r); lia).
rewrite !Z_to_bv_bv_unsigned. symmetry. exact (ho_reg_idx TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC r Hr0).
- symmetry. exact (vmatch_sound two e0 sv0 Htwo C).
Qed.
Definition G_main (two : bool) : facts :=
mkFacts ((8%nat, mkAF 1 4194303 0) :: f_atoms (G0 two)) [] [].
Lemma facts_ok_main : forall two, two_ok two -> YP0m.facts_ok EL (G_main two).
Proof.
intros two Htwo.
assert (FI : YP0m.facts_ok EL (G0 two))
by (exact (YP08.facts_ok_init TSEGS TPH inp mbase Asan.M.init_pc sp brk rdraw Hsp Hva Hve Hvl Hlau WSTK ltac:(unfold WSTK; lia) xwE xdE xdE_uid xdE_hwcap xdE_rand xdE_gid xdE_ehdr xdE_execfn two Htwo)).
destruct FI as (FA & _ & _).
split; [|split; exact I]. cbn [f_atoms G_main]. split; [|exact FA].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EL8. pose proof tid_range. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Definition ss_main (two : bool) : sstate := mkSS TFIB_MAIN sregs_main (smem_main two) None (G_main two).
Theorem st_ok_main : forall two, two_ok two ->
YP0l.st_ok TSEGS EL (ss_main two) (restrict H1 (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom TSEGS))).
Proof.
intros two Htwo. unfold YP0l.st_ok, restrict, mkst, ss_main.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (regs_ok_main two Htwo)|]. split; [exact (mem_ok_main two Htwo) | exact (facts_ok_main two Htwo)].
Qed.
Lemma H1_off : H_off_segments TSEGS H1.
Proof. intros a Ha. apply (ho_H_off TSEGS TFIB TOP argH tfib_in_hull TOPok tfib_hull_ok ARGH E ch model). exact (H1_sub a Ha). Qed.
Definition W1 : world TSEGS := mkW TSEGS H1 (allowA TFIB E ch) H1_off (ho_A_wf TFIB E ch).
Theorem AI_main : AI TSEGS (w_H W1) (w_A W1) model.
Proof.
cbn [w_H w_A W1].
apply (AI_hsub TSEGS HID); [exact (ho_AI TSEGS TFIB LIM TOP SINV argH (in_fs inp) tfib_in_hull TOPok tfib_hull_ok ARGH E ch R FULL model HC) | exact H1_sub |].
intros w Hh Hw Hl.
unfold H1 in Hw. rewrite Hh in Hw. cbn in Hw. apply andb_false_iff in Hw as [Hw|Hw]; apply negb_false_iff in Hw; [| exact (SL_allowed w Hw)].
exfalso.
pose proof (ARGH E w Hw) as Hc.
pose proof (ho_lazyb TSEGS TFIB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) as LB.
unfold page_in_ranges in Hl. apply existsb_exists in Hl as (iv & Hiv & Hin).
pose proof (proj1 (Forall_forall _ _) LB iv Hiv) as [_ B2].
apply andb_prop in Hin as [I1 I2]. apply Z.leb_le in I1. apply Z.leb_le in I2.
assert (PB : bv_unsigned w < bv_unsigned (page_base w) + 4096).
{ unfold page_base, page_base_of. rewrite Z_to_bv_unsigned. pose proof (bv_unsigned_in_range 64 w) as Hw64. change (bv_modulus 64) with (2 ^ 64) in Hw64.
unfold page_size. pose proof (Z.div_mod (bv_unsigned w) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (bv_unsigned w) 4096 ltac:(lia)).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small; nia. }
unfold page_size in *. lia.
Qed.
Lemma fs_main : m_fs model = in_fs inp.
Proof. exact (ho_fs TSEGS TFIB LIM TOP _ _ (in_fs inp) E ch R FULL model HC). Qed.
Lemma fds_main : m_fds model = fds_std.
Proof. exact (ho_fds_std TSEGS TFIB LIM TOP _ _ (in_fs inp) E ch R FULL model HC (proj1 (proj2 (proj2 (proj2 (CHK_parts true)))))). Qed.
Lemma pc_main : pc ch = TFIB_MAIN.
Proof. exact (proj2 (proj2 (proj2 (proj2 (CHK_parts true))))). Qed.
Theorem tfib_main_entry :
pc ch = TFIB_MAIN
/\ (forall two, two_ok two ->
YP0l.st_ok TSEGS EL (ss_main two) (restrict (w_H W1) (mkst R (Z_to_bv 64 TFIB_MAIN) FULL (seg_rom TSEGS)))
/\ runs_at usp (mrestrict (w_H W1) FULL) (runs_main_tfa two sp (ed_top rdraw) argv envp (in_execfn inp)))
/\ AI TSEGS (w_H W1) (w_A W1) model
/\ m_fs model = in_fs inp /\ m_fds model = fds_std
/\ u eSp0 = usp /\ bv_unsigned (ew EL 8) = bv_unsigned (ev E TIDV) /\ ew EL CANARY_ATOM = ev E CANV.
Proof.
split; [exact pc_main|].
split; [intros two Htwo; split; [exact (st_ok_main two Htwo) | exact (runs_main_m1 two Htwo)]|].
split; [exact AI_main|]. split; [exact fs_main|]. split; [exact fds_main|]. split; [exact uS0|]. split; reflexivity.
Qed.
End t.
End g.
