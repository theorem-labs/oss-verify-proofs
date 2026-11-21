(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the new stack geometry: runs_main_tfa reads the strings block up to the entry draw's top, ending in the execfn string, in place of strings then random bytes, and argH_range2's string window ends at that top; the TRB main-entry section takes the mmap base and the launch premises valid_launch and entry_launch_ok_va in place of entry_stack_fits, with SINV0, argH0, E0 and wrap_mem over the run's ProcInput and the layout environment at the entry draw's top, the run's CONFIG_RSEQ flag and execfn string; slot 4 read as the stack pad block_pad_len in ev4 and the gap word in ev9; layout_facts with eight conjuncts; the image's entry pc TPC for wrap_mem; the spellings, the value table and the per-state checks taken at the run's CONFIG_RSEQ setting, argv[0] and AT_RANDOM at the head size 472 + 32 r with the gap word, over the hand-off states computed in YB01r.v, with the thread-id and canary variables read from those states and the stack window fact at stack_window_depth). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.cgif.cgif_rgb_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require YK1b PlanRegen.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YQ0j YQ0b YQ0i YQ0a YQ04 YO3p YK00 YK05 YA0i YA0l YK0d YK0e YK0f YK0g
YK0a YA01 YA0c YA0e YA0d YA02 YA0j YB11 YB1g YB12 YB01r YD2f YD1e.
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
   [BS + HEAD rz] (YK0a.e_str0), argv[1] is [argv[0] + V_L0 + 1] (YK0a.e_str1), and the
   AT_RANDOM bytes are [BR + HEAD rz - 16] (YK0a.e_atrandom), at the run's own CONFIG_RSEQ flag
   [rz] ([HEAD rz] is [block_head_size] less the argv/envp words and the gap word, YA02.chead_eq).
   The form of reac-pw/fuzz_segconf's lib/A/AD2i.v; this unit's spellings are read from its
   computed hand-off states (YB01r.v) by a probe, and [entry_check_all] checks them by computation. *)
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
Lemma z_argv1_eq : forall t (av ev : list (list byte)) xf, (1 <= length av)%nat ->
z_argv t av ev xf 1 = z_strs t av ev xf + Z.of_nat (length (nth 0 av [])) + 1.
Proof.
intros t av ev xf H. unfold z_argv. rewrite (YQ0a.tab_firstn_S av 0) by lia.
rewrite firstn_O. change (total_arg_bytes_nat []) with 0%nat. lia.
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
   (the released 43 and 60 named the recorded states' variables); every computed state, at both
   CONFIG_RSEQ flags, holds [KRange (EVar TIDV) 1 4194303] and [EVar CANV] at the canary cells of
   [IMG_REGIONS]: read from this unit's hand-off probe, and [entry_check_all] checks it by
   computation. *)
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
[ SLit 0; SLit 598348; SOff 0 (-48); SLit 67584; SLit 6152720; SOff 14 0; SOff 15 0; SOff 16 0;
SOff 0 8; SOff 3 0; SOff 3 0; SOff 0 8; SOff 4 0; SOff 22 0; SOff 23 0; SOff 24 0;
SOff 25 0; SOff 26 0; SLit 527824; SOff 4 0; SLit 0; SLit 0; SLit 0; SLit 0;
SLit 0; SLit 0; SLit 0; SLit 0; SOff 37 0; SOff 38 0; SOff 39 0; SOff 40 0 ].
Definition rcheck (two : bool) (rz : Z) (ch : acs) (i : nat) : bool :=
let s := nth i sregs_main (SLit 0) in let e := nth i (s_regs (a_ss ch)) (ELit 0) in
(match s with SOff n 0 => (n =? 9 + i)%nat | _ => false end || vmatch two rz e s)%bool.
Definition wok (w : N) : bool := ((w =? 1) || (w =? 2) || (w =? 4) || (w =? 8))%N.
Definition cjust (two : bool) (rz : Z) (ch : acs) (ob : option nat) (c : YQ0b.chunk) : bool :=
existsb (fun sp : expr * Z => let (rb, d) := sp in
match YQ0b.c_val c with
| CVal w s => (wok w && match kn_read TSEGS ch rb (YQ0b.c_off c + d) (N.to_nat w) with Some v => vmatch two rz v s | None => false end)%bool
| CZero l => kn_zcover TRB_BSS ch rb (YQ0b.c_off c + d) l
| CImg l => match ob with
| None => (kn_img ch (YQ0b.c_off c) l && (0x10000 <=? YQ0b.c_off c) && (YQ0b.c_off c + l <=? 0x600000) && (0 <=? l))%bool
| Some _ => false end
| CData _ _ _ => false
end) (spellings rz ob).
(* LPS 727298f3: the start state's stack write fact is [KWr (SA e_sp0 (-stack_window_depth))
   (ELit stack_window_depth)] (YK0a.init_kn_with), where [stack_window_depth = stack_max_size -
   stack_window_reach] = 8388608 - 2244095 (YK1b.v); the released 8388608 was the whole
   [stack_max_size].  Every computed hand-off state holds it: [entry_check_all] checks it by
   computation. *)
Definition WDEPTH : Z := 6144513.
Lemma WDEPTH_eq : WDEPTH = YK1b.stack_window_depth.
Proof. rewrite YK1b.stack_window_depth_val. reflexivity. Qed.
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
Definition wjust (ch : acs) (r : YQ0b.region) : bool :=
((r_whi r <=? r_wlo r)
|| match r_base r with
| None => (0xa2000 <=? r_wlo r) && (r_whi r <=? 0x600000)
| Some 0%nat => kn_mem KWR_STACK ch && (- WDEPTH <=? r_wlo r) && (r_whi r <=? 0)
| Some _ => false
end)%bool.
Definition rjust (two : bool) (rz : Z) (ch : acs) (r : YQ0b.region) : bool :=
(forallb (cjust two rz ch (r_base r)) (r_chunks r) && wjust ch r
&& match r_base r with None => (0 <=? r_lo r) && (r_hi r <=? 2 ^ 47) | Some 0%nat => (- 2 ^ 40 <=? r_lo r) && (r_hi r <=? 2 ^ 40)
| Some 6%nat => (0 <=? r_lo r) && (r_hi r <=? 16) | _ => false end)%bool.
Definition R_stk : YQ0b.region := YQ0b.mkRegion (Some 0%nat) (- WSTK) 0 (- WSTK) 0 [].
Definition TRB_MAIN : Z := 0x80dd0.
(* #38: the entry pc of this image as the [pc : N] that YQ0a's Section t takes
   (YQ0a.v:392); [a_entry TRB] is the same number written as a Z, which is the
   spelling the start-up theorem hands the memory down in (YB1m.v:87).  The
   bridge is proved once, here, and used by [m1_pristine]. *)
Definition TPC : N := AsanUbsan.M.init_pc.
Lemma tpc_entry : Z.of_N TPC = a_entry TRB.
Proof. reflexivity. Qed.
Definition entry_check (two : bool) (rz : Z) (ch : acs) : bool :=
(kn_mem (KRange (EVar TIDV) 1 4194303) ch
&& forallb (rjust two rz ch) (R_stk :: R_hdr two :: IMG_REGIONS)
&& forallb (rcheck two rz ch) (seq 0 32)
&& afd_eqb (a_fd ch) FdStd && Z.eqb (pc ch) TRB_MAIN)%bool.
(* LPS 727298f3: each flag's computed hand-off states are checked at that flag's spellings. *)
Lemma entry_check_all : forall b, forallb (fun ch => entry_check true (rseq_z b) ch && entry_check false (rseq_z b) ch)
(HS_trb_list_r (rseq_z b)) = true.
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma HS_trb_r_In_r : forall r h ch, HS_trb_r r h = Some ch -> In ch (HS_trb_list_r r).
Proof.
intros r h ch H. unfold HS_trb_r, PlanRegen.hlookup in H.
destruct (find (fun q => Nat.eqb (fst q) h) (HSL_r r)) as [q|] eqn:F; [|discriminate H].
injection H as <-. apply find_some in F as [F _].
unfold HS_trb_list_r. exact (in_map snd _ _ F).
Qed.
(* 08b1429: THE STACK GEOMETRY INVERTED.  The strings now sit at the TOP of the
   entry block and run up to [ed_top rnd] ([YQ0a.stack_tail], YQ0a.v:384-385),
   while the 16 AT_RANDOM bytes moved DOWN into the head ([z_rand], YQ0a.v:206,
   and [lay_strs], :460).  So the old [stack_strs]/[pad_len] pair is gone - both
   name quantities the model no longer has - and the tail entry is
   strings-to-top rather than strings-then-random.  [envp_block] is measured
   from the top and carries the execfn (YO3p.v:109-110); only [z_envp] keeps
   [sp], because the envp POINTER ARRAY still sits just above sp.  This is
   deliberately YO3p's [runs_main] shape (YO3p.v:111-119) minus its unused
   [rnd], which is the shape YD0g.v:68 and the whole YD family are written
   against. *)
Definition runs_main_tfa (two : bool) (sp top : word) (av ev : list (list byte)) (xf : list byte) : list (Z * list byte) :=
(z_envp (bv_unsigned sp) av, envp_block top av ev xf)
:: (z_argv (bv_unsigned top) av ev xf 0, nth 0 av [] ++ [NUL])
:: (if two then [(z_argv (bv_unsigned top) av ev xf 1, nth 1 av [] ++ [NUL])] else [])
++ [(z_strs (bv_unsigned top) av ev xf, YQ0a.stack_tail av ev xf)].
Section g. Context {fx : YK11.FPState}.
Section t.
Variables (sp : word) (rdraw : EntryDraw) (brk mbase : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvl : valid_launch inp.
(* #38: [entry_stack_fits] is gone from YA02's section - YA02.v:48-57 lists the
   eleven hypotheses it now has and that is not among them - and every layout
   fact is taken off the launch instead, here as at YQ0a.v:410 and YA02.v:57. *)
Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp.
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_trb_r (rseq_z (kb_rseq (in_kernel inp))) h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation xfn := (in_execfn inp) (only parsing).
(* the run's CONFIG_RSEQ flag, never a literal (rules 12f, 12r) *)
#[local] Notation rsq := (kb_rseq (in_kernel inp)) (only parsing).
#[local] Notation RZ := (rseq_z (kb_rseq (in_kernel inp))) (only parsing).
#[local] Notation top := (ed_top rdraw) (only parsing).
#[local] Notation zt := (bv_unsigned (ed_top rdraw)) (only parsing).
(* #38: YA02's section is over the run, and [E0]/[argH0]/[SINV0] discharge as
   YB1m.v:84-88 spells them - [SINV0 TRB TPH sp rdraw brk mbase inp],
   [argH0 sp rdraw inp], [E0 sp rdraw brk inp].  [uid] and [hw] leave: they come
   off [inp] now. *)
#[local] Notation SINV := (YA02.SINV0 TRB TPH sp rdraw brk mbase inp).
#[local] Notation argH := (YA02.argH0 sp rdraw inp).
#[local] Notation TOP := (YA02.TOP sp).
#[local] Notation LIM := YA02.LIMIT.
Hypothesis HC : cs_ok TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model.
Hypothesis HE : forall n, (n < NX0G)%nat -> ev E n = ev (YA02.E0 sp rdraw brk inp) n.
Hypothesis HM : forall a, argH E a = true -> FULL a = wrap_mem inp mbase TPH (Z_to_bv 64 (a_entry TRB)) sp rdraw a.
Hypothesis SL_allowed : forall a, sliverb sp a = true -> page_allowedb (allowA TRB E ch) (page_base a) = true.
#[local] Notation MR := (Mr TRB TOP argH E ch model FULL).
#[local] Notation HID := (hid TRB TOP argH E ch model).
Let TOPok : top_ok TOP := YA02.top_ok0 sp Hsp.
Let ARGH : forall E0 (a : word), argH E0 a = true -> TOP <= bv_unsigned a := YA02.argH0_high sp rdraw inp Hsp Hva.
#[local] Notation u := (uE E).
#[local] Notation usp := (bv_unsigned sp).
Definition xwE (n : nat) : word :=
match n with
| 8%nat => ev E TIDV
| _ => if ((9 <=? n) && (n <=? 40))%nat then getr R (Z_to_bv 5 (Z.of_nat (n - 9)))
else if (n =? CANARY_ATOM)%nat then ev E CANV else Z_to_bv 64 0
end.
Definition xdE (d : nat) : list byte := if Nat.eqb d UID_DATOM then uid_bytes (in_uid inp) else [].
Definition EL : YQ0j.env := YQ0a.E0 sp top rsq argv envp xfn xwE xdE.
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
(* #38: slot 4 of [YA02.vals0] is [W], the arch_align_stack pad in BYTES
   (YA02.v:121 and :124), where it used to be a word count derived from
   [rand_off].  [rand_off] has ZERO lines in the model at 75d69e00, so this is a
   RESTATEMENT and not a re-threading: the residue the old lemma computed - and
   with it the literal 184, which was [24 + auxv_size] under the ten-pair table
   - ceases to exist rather than retabling.  The whole
   [length_bsb]/[rand_off_eq]/[rand_off_mod8]/[rand_off_bound]/[struct_size_eq]
   chain that proved it goes with it. *)
Lemma ev4 : bv_unsigned (ev E 4) = Z.of_nat (block_pad_len rsq sp top argv envp xfn).
Proof.
assert (HW : 0 <= Z.of_nat (block_pad_len rsq sp top argv envp xfn) <= 4110)
by (eapply YA02.pad_range; eassumption).
rewrite (HE 4%nat) by (unfold NX0G; lia).
cbn [ev YA02.E0 YA02.vals0 nth]. apply u64_lit. lia.
Qed.
(* [V_G] (EVar 9), the gap word count of the entry block (YA02.vals0 slot 9, YA02.gap_range). *)
Lemma ev9 : bv_unsigned (ev E 9) = Z.of_nat (block_items argv envp mod 2).
Proof.
assert (HG : 0 <= Z.of_nat (block_items argv envp mod 2) <= 1) by (eapply YA02.gap_range; eassumption).
rewrite (HE 9%nat) by (unfold NX0G; lia).
cbn [ev YA02.E0 YA02.vals0 nth]. apply u64_lit. lia.
Qed.
Lemma CHK : forall two, entry_check two RZ ch = true.
Proof.
intros two. pose proof (proj1 (forallb_forall _ _) (entry_check_all rsq) ch (HS_trb_r_In_r _ h ch Hch)) as H. cbn beta in H.
apply andb_prop in H as [H1 H2]. destruct two; [exact H1 | exact H2].
Qed.
Lemma CHK_parts : forall two,
kn_mem (KRange (EVar TIDV) 1 4194303) ch = true /\ forallb (rjust two RZ ch) (R_stk :: R_hdr two :: IMG_REGIONS) = true
/\ forallb (rcheck two RZ ch) (seq 0 32) = true /\ a_fd ch = FdStd /\ pc ch = TRB_MAIN.
Proof.
intros two. pose proof (CHK two) as H. unfold entry_check in H.
apply andb_prop in H as [H H5]. apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|apply Z.eqb_eq; exact H5].
destruct (a_fd ch); [reflexivity | discriminate H4 | discriminate H4].
Qed.
Lemma tid_range : 1 <= bv_unsigned (ev E TIDV) <= 4194303.
Proof.
pose proof (ho_range TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC (EVar TIDV) 1 4194303) as X.
unfold uE in X. apply X. exact (proj1 (CHK_parts true)).
Qed.
Lemma EL0 : bv_unsigned (ew EL 0) = usp.   Proof. reflexivity. Qed.
(* #38: [ew1] is now [z_strs], not [z_argv … 0] measured from sp - a statement
   change, not an arity change - and every [ew] takes the run.  Discharged by
   [eapply …; eassumption] rather than positionally: nobody can compile, and a
   hand-derived discharged-argument position is the likeliest thing to be
   wrong. *)
Lemma EL1 : bv_unsigned (ew EL 1) = z_strs zt argv envp xfn.
Proof. unfold EL. eapply YQ0a.ew1; eassumption. Qed.
Lemma EL2 : (2 <= length argv)%nat -> bv_unsigned (ew EL 2) = z_argv zt argv envp xfn 1.
Proof. intros H2. unfold EL. eapply YQ0a.ew2'; eassumption. Qed.
Lemma EL3 : bv_unsigned (ew EL 3) = Z.of_nat (length argv).
Proof. unfold EL. eapply YQ0a.ew3; eassumption. Qed.
Lemma EL4 : bv_unsigned (ew EL 4) = z_envp usp argv.
Proof. unfold EL. eapply YQ0a.ew4; eassumption. Qed.
Lemma EL5 : bv_unsigned (ew EL 5) = z_auxv usp argv envp.
Proof. unfold EL. eapply YQ0a.ew5; eassumption. Qed.
Lemma EL6 : bv_unsigned (ew EL 6) = z_rand usp rsq argv envp.
Proof. unfold EL. eapply YQ0a.ew6; eassumption. Qed.
Lemma EL8 : ew EL 8 = ev E TIDV.   Proof. reflexivity. Qed.
Lemma EL41 : ew EL CANARY_ATOM = ev E CANV.   Proof. reflexivity. Qed.
Lemma ELF : forall n, (9 <= n <= 40)%nat -> ew EL n = getr R (Z_to_bv 5 (Z.of_nat (n - 9))).
Proof.
intros n Hn. unfold EL, YQ0a.E0. cbn [ew].
destruct n as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; try lia. unfold xwE.
replace ((9 <=? S (S (S (S (S (S (S (S (S n))))))))) && (S (S (S (S (S (S (S (S (S n)))))))) <=? 40))%nat with true
by (symmetry; apply andb_true_iff; split; apply Nat.leb_le; lia). reflexivity.
Qed.
(* #38: a [Local Notation], not a [Let].  [lia] compares atoms syntactically and
   never unfolds a [Let] (nor a [set]), so a [Let]-bound projection in the goal
   cannot meet a hypothesis that spells it out even though the two are
   convertible; measured, then confirmed by a farm round.  [layout_facts] now
   has EIGHT conjuncts (YQ0a.v:579-587) and DROPPED
   [z_rand zsp av ev + 16 < 2^63]: the random block moved, so that conjunct
   became [z_rand + 16 <= z_strs].  Where a bound to a power of two is needed it
   is taken from the surviving form, [z_rand_end] (YQ0a.v:618), never invented. *)
#[local] Notation LF := (YQ0a.layout_facts inp mbase sp brk rdraw Hsp Hlau).
Lemma uS0 : u eSp0 = usp.
Proof.
pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
assert (X : uE E e_sp0 = YA02.TOP sp + 8388608) by (eapply YA02.SINV0_sp0; eassumption).
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
(* LPS 727298f3: [BR + HEAD RZ - 16] is the AT_RANDOM address [z_rand], and [BS + HEAD RZ]
   is argv[0]'s first byte [z_strs] = [sp + block_head_size + block_pad_len]: the head size
   is [YA02.chead_eq], the pad and the strings' end [YA02.str0_hi]. *)
Lemma uBR : u BR + (HEAD RZ - 16) = z_rand usp rsq argv envp.
Proof.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0.
pose proof ev1 as V1. pose proof ev2 as V2. pose proof ev9 as V9. pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. rewrite uE_var in B0, B6.
assert (HG : 0 <= Z.of_nat (block_items argv envp mod 2) <= 1) by (eapply YA02.gap_range; eassumption).
assert (HCH : Z.of_nat (block_head_size rsq argv envp) = 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp)
+ 472 + 32 * RZ + 8 * Z.of_nat (block_items argv envp mod 2)) by (eapply YA02.chead_eq; eassumption).
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
Lemma uBS : u BS = usp + 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp) + V 4 + 8 * V 9.
Proof.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0.
pose proof ev1 as V1. pose proof ev2 as V2. pose proof ev4 as V4. pose proof ev9 as V9.
pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
assert (HW : 0 <= Z.of_nat (block_pad_len rsq sp top argv envp xfn) <= 4110)
by (eapply YA02.pad_range; eassumption).
assert (HG : 0 <= Z.of_nat (block_items argv envp mod 2) <= 1) by (eapply YA02.gap_range; eassumption).
pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. rewrite uE_var in B0, B6.
unfold uE in V1, V2.
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
Lemma uBS_head : u BS + HEAD RZ = z_strs zt argv envp xfn.
Proof.
pose proof uBS as HB. pose proof ev4 as V4. pose proof ev9 as V9.
assert (HT : bv_unsigned sp + Z.of_nat (block_head_size rsq argv envp)
+ Z.of_nat (block_pad_len rsq sp top argv envp xfn)
+ Z.of_nat (launch_string_bytes argv envp xfn) + 8 = zt)
by (eapply YA02.str0_hi; eassumption).
assert (HCH : Z.of_nat (block_head_size rsq argv envp) = 8 * Z.of_nat (length argv) + 8 * Z.of_nat (length envp)
+ 472 + 32 * RZ + 8 * Z.of_nat (block_items argv envp mod 2)) by (eapply YA02.chead_eq; eassumption).
unfold z_strs, HEAD. lia.
Qed.
Lemma u_BS_head : u (EAlu ALU_ADD BS (ELit (HEAD RZ))) = z_argv zt argv envp xfn 0.
Proof.
pose proof uBS_head as H0. pose proof (rseq_z_range rsq) as HR.
assert (TH : zt <= SP_HI) by (eapply YQ0a.top_hi; eassumption). unfold SP_HI in TH.
pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp xfn)).
assert (Z0 : z_argv zt argv envp xfn 0 = z_strs zt argv envp xfn)
by (unfold z_argv; rewrite firstn_O; change (total_arg_bytes_nat []) with 0%nat; lia).
rewrite Z0. unfold z_strs in *. rewrite uE_add; rewrite ?uE_litv; unfold HEAD in *; lia.
Qed.
Lemma u_B5_24 : u (EAlu ALU_ADD B5 (ELit 24)) = z_auxv usp argv envp.
Proof.
pose proof uB5 as HB. pose proof LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold SP_LO, SP_HI in L7, L8.
pose proof (proj1 Hva). pose proof (proj1 Hve).
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
Lemma u_eArgv1 : (2 <= length argv)%nat -> u (eArgv1 RZ) = z_argv zt argv envp xfn 1.
Proof.
intros H2. pose proof uBS_head as H0. pose proof uBS as HB.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0.
pose proof ev1 as V1. pose proof ev2 as V2. pose proof ev3 as V3. pose proof ev4 as V4. pose proof ev9 as V9.
pose proof (proj1 Hva). pose proof (proj1 Hve). pose proof (proj1 Hsp) as L. unfold sp_window_lo in L.
pose proof LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold SP_LO, SP_HI in L7, L8. unfold z_xfn in L6.
pose proof (YQ0a.z_argv_end inp rdraw 0 ltac:(lia)) as Z0.
assert (HW : 0 <= Z.of_nat (block_pad_len rsq sp top argv envp xfn) <= 4110)
by (eapply YA02.pad_range; eassumption).
assert (HG : 0 <= Z.of_nat (block_items argv envp mod 2) <= 1) by (eapply YA02.gap_range; eassumption).
pose proof (rseq_z_range rsq) as HR.
pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat argv)). pose proof (Nat2Z.is_nonneg (total_arg_bytes_nat envp)).
pose proof (Nat2Z.is_nonneg (length xfn)).
pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. pose proof (uE_bound E (EVar 3)) as B3.
pose proof (uE_bound E (EVar 4)) as B4. rewrite uE_var in B0, B6, B3, B4.
unfold uE in V1, V2.
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
rewrite (z_argv1_eq zt argv envp xfn ltac:(lia)). lia.
Qed.
Lemma u_eEnvp : u eEnvp = z_envp usp argv.
Proof.
pose proof uSp0 as [S0 SR]. pose proof uS0 as U0. pose proof ev1 as V1.
pose proof (proj1 Hva). pose proof (uE_bound E (EVar 0)) as B0. pose proof (uE_bound E (EVar 6)) as B6. rewrite uE_var in B0, B6. unfold uE in V1.
pose proof LF as (L1 & _ & _ & _ & _ & _ & L7 & L8). unfold SP_LO, SP_HI in L7, L8.
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
- destruct Hin as [Hin|[]]. injection Hin as <- <-. cbn [base_val]. pose proof LF as (L1 & L2 & _). rewrite EL5, uB5. lia.
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
+ rewrite EL1, edenot_uE, u_BS_head. pose proof LF as (_ & _ & _ & _ & L5 & _). rewrite L5. reflexivity.
+ rewrite EL5, edenot_uE, u_B5_24. reflexivity.
+ change (edenot E (EVar 8)) with (ev E 8). rewrite ev8. unfold data_word. cbn [ed EL YQ0a.E0 xdE Nat.eqb UID_DATOM N.to_nat Z.to_nat skipn].
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
Let Hbyte := ho_read_byte TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Let Hbound := ho_read_bound TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Let Hzc := ho_zcover_range TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC TRB_BSS trb_bss_rom.
Let Himg := ho_img_at TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC.
Lemma hreader_mbyte : forall a z, hreader TSEGS MR a = Some z -> exists b : byte, mbyte TSEGS MR a = Some b /\ bv_unsigned b = z.
Proof.
intros a z H. unfold hreader in H. destruct (mbyte TSEGS MR a) as [b|]; [|discriminate H]. cbn in H. injection H as <-.
exists b. split; reflexivity.
Qed.
Lemma cjust_sound : forall (two : bool) ob c, two_ok two ->
cjust two RZ ch ob c = true -> chunk_ok TSEGS EL MR (base_val EL ob) c.
Proof.
intros two ob [off cv] Htwo H. unfold cjust in H. apply existsb_exists in H as ([rb d] & Hspl & H).
pose proof (spellings_sound ob rb d Hspl) as HB. cbn [YQ0b.c_val YQ0b.c_off] in H.
intros i Hi. unfold YQ0b.c_len in Hi. cbn [YQ0b.c_off YQ0b.c_val] in Hi |- *.
destruct cv as [w sv0|l|l|dd ss ll]; cbn [YQ0b.cv_len] in Hi; try discriminate H.
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
pose proof (proj1 (Forall_forall _ _) (ho_know TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) _ HK) as (_ & _ & Hnone).
pose proof (Hnone (off + i) ltac:(lia)) as X.
cbn [cbyte]. unfold img_byte, mbyte. rewrite Z.add_0_l. rewrite X.
destruct (seg_rom TSEGS (Z_to_bv 64 (off + i))) as [b|] eqn:Hs; [exists b; split; reflexivity|].
exfalso. exact (trb_rom_all (off + i) ltac:(lia) Hs).
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
pose proof (ho_wr TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC _ _ H1 (o + WDEPTH) 1%nat ltac:(unfold WDEPTH in *; lia)) as W.
unfold elenZ in W. cbn [edenot] in W. rewrite u64_lit in W by (unfold WDEPTH; lia). specialize (W ltac:(unfold WDEPTH in *; lia)).
unfold estart in W. cbn [a_base a_off] in W. fold (u eSp0) in W. rewrite uS0 in W.
replace (usp + - WDEPTH + (o + WDEPTH)) with (usp + o) in W by lia. exact (store_ok1_wview _ _ W).
- discriminate H.
- apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn [base_val].
unfold writable_at. apply trb_rw_window. rewrite u64_lit by lia. lia.
Qed.
Lemma rjust_sound : forall two r, two_ok two -> rjust two RZ ch r = true -> region_ok TSEGS EL MR r.
Proof.
intros two r Htwo H. unfold rjust in H. apply andb_prop in H as [H HB]. apply andb_prop in H as [HC0 HW].
pose proof LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold SP_LO, SP_HI in L7, L8.
(* base 6 is [z_rand] ([EL6]); its end below 2^63 is YQ0a's [z_rand_end] (the stack layout) *)
assert (ZR : z_rand usp rsq argv envp + 16 < 2 ^ 63) by (eapply YQ0a.z_rand_end; eassumption).
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
(* #38: [wrap_mem] migrated to the run (YQ0a.v:404) - [inp mbase ph entry sp rnd],
   with the entry as a word.  Spelt here at [Z.of_N TPC] so that YQ0a's Section t
   lemmas, whose [m0] is [Z_to_bv 64 (Z.of_N pc)], unify by [pc := TPC] with no
   hand-supplied argument; [HM] arrives in the start-up theorem's own spelling
   [a_entry TRB] (YB1m.v:87) and [m1_pristine] bridges the two once. *)
#[local] Notation m0 := (wrap_mem inp mbase TPH (Z_to_bv 64 (Z.of_N TPC)) sp rdraw).
Lemma H1_sub : hsub H1 HID.
Proof. intros a Ha. unfold H1 in Ha. apply andb_prop in Ha as [Ha _]. apply andb_prop in Ha as [Ha _]. exact Ha. Qed.
Lemma MR_m1 : forall a b, MR a = Some b -> m1 a = Some b.
Proof.
intros a b H. rewrite Mr_is_mrestrict in H. unfold mrestrict, H1 in *.
destruct (hid TRB TOP argH E ch model a); [discriminate H|]. cbn. exact H.
Qed.
Lemma mbyte_MR_m1 : forall a b, mbyte TSEGS MR a = Some b -> mbyte TSEGS m1 a = Some b.
Proof.
intros a b H. unfold mbyte in *. destruct (MR (Z_to_bv 64 a)) as [b'|] eqn:E1.
- rewrite (MR_m1 _ _ E1). exact H.
- rewrite Mr_is_mrestrict in E1. unfold mrestrict in E1. unfold mrestrict, H1.
destruct (hid TRB TOP argH E ch model (Z_to_bv 64 a)) eqn:Eh.
+
exfalso. pose proof (ho_hid_off TSEGS TRB TOP argH trb_in_hull TOPok trb_hull_ok ARGH E ch model _ Eh) as Hoff.
rewrite (seg_rom_none_of_find TSEGS _ Hoff) in H. discriminate H.
+ cbn. rewrite E1. exact H.
Qed.
Lemma wview_MR_m1 : forall a, wview TSEGS MR a <> None -> wview TSEGS m1 a <> None.
Proof.
intros a H. unfold wview in *. destruct (MR a) as [b|] eqn:E1.
- rewrite (MR_m1 _ _ E1). discriminate.
- rewrite Mr_is_mrestrict in E1. unfold mrestrict in E1. unfold mrestrict, H1.
destruct (hid TRB TOP argH E ch model a) eqn:Eh.
+ exfalso. pose proof (ho_hid_off TSEGS TRB TOP argH trb_in_hull TOPok trb_hull_ok ARGH E ch model _ Eh) as Hoff.
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
Proof.
intros a Ha. unfold mrestrict, H1. rewrite Ha. cbn. rewrite andb_false_r. cbn.
(* [cbn] above computes [Z.of_N TPC] away, so the bridge is used right to left,
   on the [a_entry TRB] that [HM] brings in, and the two numbers meet by
   conversion. *)
rewrite (HM a Ha). rewrite <- ?tpc_entry. reflexivity.
Qed.
(* #38: THE GEOMETRY INVERTED, so this window is a RESTATEMENT, not a
   re-threading.  [YA02.argH0]'s second disjunct is [STR0 <= z < utop] with
   [STR0 = usp + CHEAD + W] (YA02.v:122, :129-132), and [YA02.str0_hi] (:269)
   gives [STR0 + LSTR + 8 = utop], i.e. [STR0 = z_strs zt av ev xf]
   (YQ0a.v:197-198).  The strings therefore run UP TO THE TOP: the old upper
   bound [z_rand] is wrong, because the random block moved BELOW them into the
   head (YQ0a.v:206 and the surviving [lay_strs], :460).  [rand_off],
   [rand_off_bound], [rand_off_mod8], [struct_size_eq] and [length_bsb] are all
   gone from the model, and with the subtraction they served. *)
Lemma argH_range2 : forall z, z_strs zt argv envp xfn <= z < zt -> argH E (Z_to_bv 64 z) = true.
Proof.
intros z Hz.
assert (HT : bv_unsigned sp + Z.of_nat (block_head_size rsq argv envp)
+ Z.of_nat (block_pad_len rsq sp top argv envp xfn)
+ Z.of_nat (launch_string_bytes argv envp xfn) + 8 = zt)
by (eapply YA02.str0_hi; eassumption).
assert (SL : SP_LO <= z_strs zt argv envp xfn) by (eapply YQ0a.strs_lo; eassumption).
assert (TH : zt <= SP_HI) by (eapply YQ0a.top_hi; eassumption).
unfold SP_LO, SP_HI in SL, TH.
unfold argH0. cbv beta zeta.
rewrite u64_lit by lia.
apply orb_true_iff. right. apply andb_true_iff.
unfold z_strs in *.
split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.
(* unchanged in meaning: the envp POINTER ARRAY still sits just above sp, so
   [argH0]'s first disjunct is still [z_envp, z_auxv). *)
Lemma argH_range1 : forall z, z_envp usp argv <= z < z_auxv usp argv envp -> argH E (Z_to_bv 64 z) = true.
Proof.
intros z Hz. pose proof LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold SP_LO, SP_HI in L7, L8.
pose proof (proj1 Hva). pose proof (proj1 Hve).
unfold argH0. cbv beta zeta. rewrite u64_lit by (unfold z_envp, z_auxv in *; lia).
apply orb_true_iff. left. apply andb_true_iff. unfold z_envp, z_auxv in *.
split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
Qed.
Lemma bytes_at_m1 : forall a bs, YQ0a.bytes_at m0 a bs -> (forall j, (j < length bs)%nat -> argH E (Z_to_bv 64 (a + Z.of_nat j)) = true) ->
YQ04.bytes_at m1 a bs.
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
unfold mbyte in *. rewrite (m1_pristine _ (HA (base_val EL (r_base r) + YQ0b.c_off c + i) ltac:(lia))). exact Hb2.
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
pose proof (hdr_check two) as CKh. pose proof LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold SP_LO, SP_HI in L7, L8.
unfold z_xfn in L6.
unfold smem_main. apply Forall_app. split; [|apply Forall_app; split].
- constructor; [apply region_ok_MR_m1; exact (rjust_sound two _ Htwo CKs)|].
constructor; [apply region_ok_MR_m1; exact (rjust_sound two _ Htwo CKh)|].
constructor; [|constructor].
apply region_ok_pristine; [eapply YQ0a.region_ok_argv0; eassumption | cbn; lia | | reflexivity].
cbn [r_base r_lo r_hi R_argv0 base_val]. rewrite EL1. intros a Ha. apply argH_range2. lia.
- destruct two; [|constructor]. constructor; [|constructor]. unfold two_ok in Htwo.
apply region_ok_pristine; [eapply YQ0a.region_ok_argv1; eassumption | cbn; lia | | reflexivity].
cbn [r_base r_lo r_hi R_argv1 base_val]. rewrite (EL2 Htwo). intros a Ha. apply argH_range2.
pose proof (YQ0a.z_argv_bounds inp rdraw 1 Htwo) as [Z1a Z1b]. lia.
- apply Forall_forall. intros r Hr. apply region_ok_MR_m1. apply (rjust_sound two _ Htwo). exact (proj1 (forallb_forall _ _) CKi r Hr).
Qed.
Definition ext_disj_abs (r1 r2 : YQ0b.region) : bool :=
match r_base r1, r_base r2 with
| None, None => (r_hi r1 <=? r_lo r2) || (r_hi r2 <=? r_lo r1)
| _, _ => false
end%bool.
Fixpoint all_disj_abs (r : YQ0b.region) (rs : smem) : bool :=
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
Lemma img_regions_abs : forallb (fun r => match r_base r with None => (0 <=? r_lo r) && (r_hi r <=? 0x600000) | _ => false end)%bool IMG_REGIONS = true.
Proof. vm_compute. reflexivity. Qed.
Lemma img_region_shape : forall r, In r IMG_REGIONS -> r_base r = None /\ r_hi r <= 0x600000.
Proof.
intros r Hr. pose proof (proj1 (forallb_forall _ _) img_regions_abs r Hr) as H. cbn beta in H.
destruct (r_base r); [discriminate H|]. apply andb_prop in H as [_ H]. apply Z.leb_le in H. split; [reflexivity | exact H].
Qed.
Lemma smem_main_disjoint : forall two, two_ok two -> pairwise_disjoint EL (smem_main two).
Proof.
intros two Htwo. pose proof LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold SP_LO, SP_HI in L7, L8.
unfold z_xfn in L6.
pose proof (proj1 Hva) as HA. pose proof EL0 as E0'. pose proof EL1 as E1'. pose proof EL6 as E6'.
assert (SL : SP_LO <= z_strs zt argv envp xfn) by (eapply YQ0a.strs_lo; eassumption).
unfold SP_LO in SL.
pose proof (YQ0a.z_argv_bounds inp rdraw 0 ltac:(lia)) as [B0a B0b].
(* #38: the random block is no longer the upper fence of the string area - it
   sits BELOW it now - so [R_argv1]'s separation from the image regions is taken
   from [strs_lo] (YQ0a.v:630) rather than from [z_rand]. *)
assert (TWO : forall r, In r (if two then [R_argv1] else []) ->
two = true /\ r = R_argv1 /\ bv_unsigned (ew EL 2) = z_argv zt argv envp xfn 1
/\ z_argv zt argv envp xfn 0 + 1 <= z_argv zt argv envp xfn 1
/\ z_strs zt argv envp xfn <= z_argv zt argv envp xfn 1).
{ intros r Hr. destruct two; [|destruct Hr]. destruct Hr as [<-|[]]. unfold two_ok in Htwo.
pose proof (YQ0a.z_argv_bounds inp rdraw 1 Htwo) as [B1a B1b].
pose proof (YQ0a.tab_firstn_S argv 0 ltac:(lia)) as TS. rewrite firstn_O in TS.
split; [reflexivity|]. split; [reflexivity|]. split; [exact (EL2 Htwo)|]. split; [|exact B1a].
unfold z_argv. rewrite firstn_O. lia. }
unfold smem_main.
apply YQ0a.pairwise_disjoint_app; [|apply YQ0a.pairwise_disjoint_app|].
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
YQ04.bytes_at m a l1 -> YQ04.bytes_at m (a + Z.of_nat (length l1)) l2 -> YQ04.bytes_at m a (l1 ++ l2).
Proof.
intros m a l1 l2 B1 B2 j Hj. rewrite length_app in Hj.
destruct (Nat.lt_ge_cases j (length l1)) as [Hl|Hg].
- rewrite nth_error_app1 by exact Hl. apply B1. exact Hl.
- rewrite nth_error_app2 by exact Hg.
replace (a + Z.of_nat j) with (a + Z.of_nat (length l1) + Z.of_nat (j - length l1)) by lia. apply B2. lia.
Qed.
(* #38: [stack_strs_end] is gone with [stack_strs].  Its replacement is
   [YQ0a.stack_tail_end] (YQ0a.v:565), which says the tail ends AT [ed_top rnd]
   rather than at the random block, and which discharges [inp rnd] only. *)
Theorem runs_main_m1 : forall two, two_ok two -> runs_at usp m1 (runs_main_tfa two sp top argv envp xfn).
Proof.
intros two Htwo. pose proof LF as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8). unfold SP_LO, SP_HI in L7, L8.
unfold z_xfn in L6.
pose proof (proj1 Hva) as HA. pose proof (proj1 Hve) as HEv.
assert (SL : SP_LO <= z_strs zt argv envp xfn) by (eapply YQ0a.strs_lo; eassumption).
unfold SP_LO in SL.
assert (TE : z_strs zt argv envp xfn + Z.of_nat (length (YQ0a.stack_tail argv envp xfn)) = zt)
by (eapply YQ0a.stack_tail_end; eassumption).
unfold runs_main_tfa. cbn [app]. apply Forall_cons; [|apply Forall_cons; [| apply Forall_app; split]].
- cbn [fst snd]. rewrite YO3p.length_envp_block.
split; [lia|]. split; [lia|]. unfold envp_block, envp_words. rewrite flat_map_app. apply bytes_at_app'.
+ apply bytes_at_m1; [apply (YQ0a.m0_envp_ptrs TPH inp TPC mbase sp brk rdraw Hsp Hlau)|].
rewrite length_flat_map_le8, length_string_addrs_fst. intros j Hj. apply argH_range1. lia.
+ rewrite length_flat_map_le8, length_string_addrs_fst. cbn [flat_map]. rewrite app_nil_r.
replace (z_envp usp argv + Z.of_nat (8 * length envp)) with (z_auxv usp argv envp - 8) by lia.
apply bytes_at_m1; [apply (YQ0a.m0_envp_null TPH inp TPC mbase sp brk rdraw Hsp Hlau)|].
rewrite length_n_to_le_8. intros j Hj. apply argH_range1. lia.
- cbn [fst snd]. pose proof (YQ0a.z_argv_bounds inp rdraw 0 ltac:(lia)) as [Ba Bb].
rewrite length_app. cbn [length]. split; [lia|]. split; [lia|].
apply bytes_at_m1; [apply (YQ0a.m0_argv_str TPH inp TPC mbase sp brk rdraw Hsp Hlau 0); lia|].
rewrite length_app. cbn [length]. intros j Hj. apply argH_range2. lia.
- destruct two; [|constructor]. unfold two_ok in Htwo. apply Forall_cons; [|constructor]. cbn [fst snd].
pose proof (YQ0a.z_argv_bounds inp rdraw 1 Htwo) as [Ba Bb].
rewrite length_app. cbn [length]. split; [lia|]. split; [lia|].
apply bytes_at_m1; [apply (YQ0a.m0_argv_str TPH inp TPC mbase sp brk rdraw Hsp Hlau 1); lia|].
rewrite length_app. cbn [length]. intros j Hj. apply argH_range2. lia.
- apply Forall_cons; [|constructor]. cbn [fst snd].
split; [lia|]. split; [lia|].
apply bytes_at_m1; [apply (YQ0a.m0_tail TPH inp TPC mbase sp brk rdraw Hsp Hlau)|].
intros j Hj. apply argH_range2. lia.
Qed.
Lemma rcheck_all : forall two, forallb (rcheck two RZ ch) (seq 0 32) = true.
Proof. intros two. exact (proj1 (proj2 (proj2 (CHK_parts two)))). Qed.
Lemma regs_ok_main : forall two, two_ok two -> YQ0i.regs_ok EL sregs_main R.
Proof.
intros two Htwo r. pose proof (rcheck_all two) as CK.
unfold YQ0i.sr_get. destruct (bv_eqb r 0) eqn:Hr0.
{ unfold getr. rewrite Hr0. reflexivity. }
rewrite (ho_reg_idx TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC r Hr0). unfold APC.reg.
assert (Hi : (YQ0i.ridx r < 32)%nat).
{ unfold YQ0i.ridx. pose proof (bv_unsigned_in_range 5 r) as X. change (bv_modulus 5) with 32 in X. lia. }
assert (Hx : AX2.ridx r = YQ0i.ridx r) by reflexivity. rewrite Hx.
pose proof (proj1 (forallb_forall _ _) CK (YQ0i.ridx r) ltac:(apply in_seq; lia)) as C. unfold rcheck in C.
set (sv0 := nth (YQ0i.ridx r) sregs_main (SLit 0)) in *. set (e0 := nth (YQ0i.ridx r) (s_regs (a_ss ch)) (ELit 0)) in *.
apply orb_prop in C as [C|C].
- destruct sv0 as [|n z| | | | | | | | |]; try discriminate C. destruct z; try discriminate C. apply Nat.eqb_eq in C. subst n.
cbn [sv_denot]. rewrite Z.add_0_r, (ELF (9 + YQ0i.ridx r)%nat) by lia.
replace (9 + YQ0i.ridx r - 9)%nat with (YQ0i.ridx r) by lia. unfold YQ0i.ridx. rewrite Z2Nat.id by (pose proof (bv_unsigned_in_range 5 r); lia).
rewrite !Z_to_bv_bv_unsigned. symmetry. exact (ho_reg_idx TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC r Hr0).
- symmetry. exact (vmatch_sound two e0 sv0 Htwo C).
Qed.
Definition G_main (two : bool) : facts :=
mkFacts ((8%nat, mkAF 1 4194303 0) :: f_atoms (G0 two)) [] [].
Lemma facts_ok_main : forall two, two_ok two -> YQ0j.facts_ok EL (G_main two).
Proof.
intros two Htwo.
assert (FI : YQ0j.facts_ok EL (G0 two)) by (eapply YQ0a.facts_ok_init; eassumption).
destruct FI as (FA & _ & _).
split; [|split; exact I]. cbn [f_atoms G_main]. split; [|exact FA].
unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite EL8. pose proof tid_range. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia.
Qed.
Definition ss_main (two : bool) : sstate := mkSS TRB_MAIN sregs_main (smem_main two) None (G_main two).
Theorem st_ok_main : forall two, two_ok two ->
YQ0i.st_ok TSEGS EL (ss_main two) (restrict H1 (mkst R (Z_to_bv 64 TRB_MAIN) FULL (seg_rom TSEGS))).
Proof.
intros two Htwo. unfold YQ0i.st_ok, restrict, mkst, ss_main.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [exact (regs_ok_main two Htwo)|]. split; [exact (mem_ok_main two Htwo) | exact (facts_ok_main two Htwo)].
Qed.
Lemma H1_off : H_off_segments TSEGS H1.
Proof. intros a Ha. apply (ho_H_off TSEGS TRB TOP argH trb_in_hull TOPok trb_hull_ok ARGH E ch model). exact (H1_sub a Ha). Qed.
Definition W1 : world TSEGS := mkW TSEGS H1 (allowA TRB E ch) H1_off (ho_A_wf TRB E ch).
Theorem AI_main : AI TSEGS (w_H W1) (w_A W1) model.
Proof.
cbn [w_H w_A W1].
apply (AI_hsub TSEGS HID); [exact (ho_AI TSEGS TRB LIM TOP SINV argH (in_fs inp) trb_in_hull TOPok trb_hull_ok ARGH E ch R FULL model HC) | exact H1_sub |].
intros w Hh Hw Hl.
unfold H1 in Hw. rewrite Hh in Hw. cbn in Hw. apply andb_false_iff in Hw as [Hw|Hw]; apply negb_false_iff in Hw; [| exact (SL_allowed w Hw)].
exfalso.
pose proof (ARGH E w Hw) as Hc.
pose proof (ho_lazyb TSEGS TRB LIM TOP SINV argH (in_fs inp) E ch R FULL model HC) as LB.
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
Proof. exact (ho_fs TSEGS TRB LIM TOP _ _ (in_fs inp) E ch R FULL model HC). Qed.
Lemma fds_main : m_fds model = fds_std.
Proof. exact (ho_fds_std TSEGS TRB LIM TOP _ _ (in_fs inp) E ch R FULL model HC (proj1 (proj2 (proj2 (proj2 (CHK_parts true)))))). Qed.
Lemma pc_main : pc ch = TRB_MAIN.
Proof. exact (proj2 (proj2 (proj2 (proj2 (CHK_parts true))))). Qed.
Theorem trb_main_entry :
pc ch = TRB_MAIN
/\ (forall two, two_ok two ->
YQ0i.st_ok TSEGS EL (ss_main two) (restrict (w_H W1) (mkst R (Z_to_bv 64 TRB_MAIN) FULL (seg_rom TSEGS)))
/\ runs_at usp (mrestrict (w_H W1) FULL) (runs_main_tfa two sp top argv envp xfn))
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
