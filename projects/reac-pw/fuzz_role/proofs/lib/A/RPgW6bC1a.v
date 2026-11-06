(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the first three blocks of
   case 1 of ent_build's `switch (kind % 10)` (pod.h:285-296, ent_text pod.h:209-219) inside LLVMFuzzerTestOneInput
   (0x7ff88), each an engine run (lib/Reusable/YCbn.v) from an entry state to a call or to the next block, with its
   post in the shape of lib/A/RPgW7bBase.v's w7_post. Proves no function (kind: segment lemma).

   THE CODE (registers as at a case entry, lib/A/RPgW6bBase.v w6b_in: s1 = R, s7 = SHADOW_OFF, s8 = c the cursor
   after the kind byte, a4 = c - 1, s9 = |r|, [R+0xf8] = |r| + 1):
     c1_head   0x80fd8 .. 0x81284
       0x80fd8  beqz s9 -> 0x81264                no byte left: 0x81264 sd zero,0xf8(s1); a0 := 0; a4 := s8
       0x80fdc .. 0x80fe8  the instrumented check of s8 (the shadow byte at (s8 >> 3) + s7; slow block 0x81a08)
       0x80fec  lbu a0,0(s8) (= m); [R+0xf8] := [R+0xf8] - 2; a4 := a4 + 2
       0x81000 .. 0x81018  a0 := m % 9 (mul by 0x39, srli 9, two subw, andi 0xff); j 0x81270
       0x81270  sd a4,0xc8(s1) (the cursor's spill); a0 := 0x9a500 + 8 * a0 (&vocab[i])
     c1_vcell  0x81284 .. the strlen trampoline 0x41ac8 (`jal` at 0x812a0, ra = 0x812a4)
       0x81284 .. 0x81290  the instrumented check of the 8-byte cell at a0: the shadow byte must be 0 (`beqz` to
                0x81298; else `j` to the error path 0x828b8, which the proof shows is not reached)
       0x81298  ld s11,0(a0) (= vocab[i]); mv a0,s11; jal strlen
     c1_set    0x812a4 .. __asan_memcpy 0x510d4 (`jal` at 0x812c8, ra = 0x812cc)
       s9 := len; s5 := len; bltu len,0x5f (taken: the nine lengths are 12 .. 18); s8 := [R+0xc0] (= F + 0xf8,
       &e.body); a0 := s8; a1 := s11; a2 := s5; jal __asan_memcpy
   THE STATES. Every register is its own atom (sr_atoms); the extra atoms are listed at each state. a0 at 0x81284 is
   its own atom (x10) with the fact [0x9a500, 0x9a540] (8-aligned), so the engine sees the check's
   `(x >> 3) + s7` form: a literal a0 would fold the shift away. The check's obligation `range_addressable` over
   the cell's 8 bytes is paid by the registered table's addressable range (w6b_vocab_ok). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgSteps RPgW6aBase RPgW6bBase.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgEntBKit RPgW7bBase RPgW6aTail RPgW6aC2h.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require RPgCfgChanges.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ======================================== the pcs ======================================== *)
Definition C1_V : Z := 0x81284.      (* a0 = &vocab[i]: the check of the cell and its `ld` *)
Definition C1_SLR : Z := 0x812a4.    (* strlen returns here *)
Definition C1_MCR : Z := 0x812cc.    (* __asan_memcpy returns here *)

(* ======================================== the head's states ======================================== *)
(* the facts every state shares: R = s1 (atom 9) in [alloc_ceiling's floor, 2^47], 16-aligned; s7 = K (atom 23) *)
Definition c1_fR : nat * afact := (9%nat, mkAF 0x7fff7f800000 (2 ^ 47) 4).
Definition c1_fK : nat * afact := (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
(* [R+0xc8, R+0xd0) written (the cursor's spill); [R+0xf8, R+0x100) read and written (in.n); the byte at s8 *)
Definition c1_rB : YP09.region := YP09.mkRegion (Some 9%nat) 0xc8 0xd0 0xc8 0xd0 [].
Definition c1_rC : YP09.region := YP09.mkRegion (Some 9%nat) 0xf8 0x100 0xf8 0x100 [YP09.mkChunk 0xf8 (CVal 8 (SOff 32 0))].
Definition c1_rC0 : YP09.region := YP09.mkRegion (Some 9%nat) 0xf8 0x100 0xf8 0x100 [].
Definition c1_rI : YP09.region := YP09.mkRegion (Some 24%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
(* a byte left: extra atoms 32 = [R+0xf8] = |r| + 1, 33 = m; s8 in [1, 2^47 - 1], s9 in [1, 2^47] *)
Definition c1_hf1 : facts :=
  mkFacts [c1_fR; c1_fK; (24%nat, mkAF 1 (2 ^ 47 - 1) 0); (25%nat, mkAF 1 (2 ^ 47) 0); (33%nat, mkAF 0 255 0)] [] [].
Definition c1_hss1 : sstate := mkSS W6B_D1 sr_atoms [c1_rB; c1_rC; c1_rI] None c1_hf1.
Definition c1_hx1 (n m : Z) : list word := [Z_to_bv 64 (n + 1); Z_to_bv 64 m].
(* no byte left: s9 is pinned to 0 after the entry *)
Definition c1_hf0 : facts := mkFacts [c1_fR; c1_fK] [] [].
Definition c1_hss0 : sstate := mkSS W6B_D1 sr_atoms [c1_rB; c1_rC0] None c1_hf0.
(* the bytes the head writes *)
Definition c1_head_wr (R : Z) : Z -> Prop := fun a => (R + 0xc8 <= a < R + 0xd0) \/ (R + 0xf8 <= a < R + 0x100).

(* ======================================== the arithmetic ======================================== *)
(* a0 at 0x81284 as the engine computes it from m (atom 33) *)
Definition c1_q : sv := SAlu ALU_SRL (SMd M_MUL (SOff 33 0) (SLit 57)) (SLit 9).
Definition c1_a0 : sv :=
  SAlu ALU_ADD (SLit 632064)
    (SAlu ALU_SLL (SAlu ALU_AND (SAlu ALU_SUB (SAlu ALU_SUB (SOff 33 0) c1_q) (SAlu ALU_SLL c1_q (SLit 3))) (SLit 255))
       (SLit 3)).
Lemma c1_a0_val : forall E m, ew E 33 = Z_to_bv 64 m -> 0 <= m < 256 ->
  sv_denot E c1_a0 = Z_to_bv 64 (W6B_VOCAB + 8 * (m mod 9)).
Proof.
intros E m Hm Hr.
transitivity (sv_denot (c2_envz m) c1_a0); [unfold c1_a0, c1_q; cbn [sv_denot ew c2_envz]; rewrite Hm; reflexivity|].
apply bv_eq. apply Z.eqb_eq.
exact (c2_all256 (fun m => bv_unsigned (sv_denot (c2_envz m) c1_a0) =? bv_unsigned (Z_to_bv 64 (W6B_VOCAB + 8 * (m mod 9))))
  ltac:(vm_compute; reflexivity) m Hr).
Qed.
(* a chunk of a computed region *)
Ltac c1_in := cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).
Lemma c1_vptr_range : forall i, 0 <= w6b_vptr i <= 0x20fe0.
Proof.
intros i. unfold w6b_vptr.
destruct (Z.to_nat i) as [|[|[|[|[|[|[|[|[|n]]]]]]]]]; cbn [nth]; try lia. destruct n; lia.
Qed.
Lemma c1_af : forall E n v lo hi al, bv_unsigned (ew E n) = v -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
  afact_ok E n (mkAF lo hi al).
Proof. intros E n v lo hi al H Hb Hm Ha. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite H. auto. Qed.
Lemma c1_U_extra : forall regs extra j v, nth j extra (Z_to_bv 64 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew (Ereg regs extra) (32 + j)) = v.
Proof. intros regs extra j v H Hv. rewrite ew_Ereg_extra, H. apply unsigned_lit_small. exact Hv. Qed.

(* the windows of a start state lie in Zn *)
Ltac c1_kwr B9 :=
  let a := fresh "a" in let r0 := fresh "r0" in let Hin := fresh "Hin" in let Hb := fresh "Hb" in
  intros a (r0 & Hin & Hb);
  lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r0 rs') in Hin end;
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb; rewrite ?B9 in Hb; cbv beta; try unfold c1_head_wr; lia|]);
  destruct Hin.
(* a register of a run's last state, its symbolic value computed and denoted *)
Ltac c1_reg HS r :=
  lazymatch type of HS with st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    rewrite (st_ok_restrict_reg segs H E ss ms r HS);
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    replace (sr_get (ss_regs ss) r) with e by (vm_compute; reflexivity)
  end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Hypothesis LAWS : AR_laws rsegs B.

(* ======================================== c1_head: 0x80fd8 .. 0x81284 ======================================== *)
Lemma c1_head : forall STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc (regs : bvmap 5 word) R F pos c vb pp kd r,
  w6_ctx B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc R F pos ->
  w6b_in B W memc regs R F c vb pp kd r ->
  SRr rsegs W (cfg_at rsegs W6B_D1 regs memc mdc)
  (w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k C1_V regs memc mdc [10; 11; 12; 14; 25]%bv (c1_head_wr R)
   (fun regs2 mem2 =>
     getr regs2 10 = w64 (W6B_VOCAB + 8 * (fst (fuzz_u8 r) mod 9)) /\
     val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xc8) 8
       (c + Z.of_nat (length r) - Z.of_nat (length (snd (fuzz_u8 r)))) /\
     val_mem rsegs (mrestrict (w_H W) mem2) (R + 0xf8) 8 (Z.of_nat (length (snd (fuzz_u8 r)))))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos c vb pp kd r Hctx Hin.
destruct Hctx as (HJ & HR16 & HRsp & HspR & Hown & HFa & Hrom).
destruct Hin as (H2 & H3 & H4 & H9 & H23 & H24 & H14 & H25 & H21 & H27 & H20 & Vf8 & Vb0 & Vf0 & Vc0 & V20 & V70 & V80 &
  Hvb & Hkd & Hpp1 & Hpp2 & HF1 & HF2 & HF32 & Ez & Hrae & Hhe & Hc1 & Hw6 & Hhin & HdisF).
destruct Hw6 as (Hg & Hrain & Hc0 & Hcr & Ham & Hdis).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hsp0al & HSTK0 & Hceil & Hslo & Hshi & H47 & _).
pose proof asan_consts as (Hac & _).
assert (HT : T_SEG_STK = 16384) by reflexivity. rewrite HT in HspR, Hdis.
assert (HRb : 0x7fff7f800000 <= R /\ R + 0x1a0 <= 2 ^ 47) by lia. destruct HRb as (HRb1 & HRb2).
clear Hsp0al Hceil Hslo Hshi H47 Hac.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
assert (Pw : forall o, 0xc8 <= o < 0x100 -> apresent (w_H W) memc (R + o)) by (intros o Ho; apply Hpres; lia).
destruct r as [|mb r1].
- (* no byte left: a0 = 0, the cursor c spilled, [R+0xf8] := 0 *)
  cbn [fuzz_u8 fst snd length].
  set (E := Ereg regs []).
  assert (B9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
  assert (B23 : bv_unsigned (ew E 23) = SHADOW_OFF)
    by exact (eb_U_reg regs _ 23 23%bv _ eq_refl H23 ltac:(unfold SHADOW_OFF; lia)).
  assert (B24 : bv_unsigned (ew E 24) = c) by exact (eb_U_reg regs _ 24 24%bv c eq_refl H24 ltac:(lia)).
  assert (HS : st_ok rsegs E c1_hss0 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor]].
      + unfold region_ok, c1_rB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        change (Ereg regs []) with E. rewrite B9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable rsegs). apply Pw. lia.
      + unfold region_ok, c1_rC0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        change (Ereg regs []) with E. rewrite B9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable rsegs). apply Pw. lia.
    - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, c1_rB, c1_rC0.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (Ereg regs []) with E. rewrite B9.
      split; [split; [lia | exact I] | split; exact I].
    - unfold facts_ok. cbn [c1_hf0 c1_fR c1_fK f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      change (Ereg regs []) with E.
      split; [|split; exact I]. split; [|split; [|exact I]].
      + apply (c1_af _ _ R _ _ _ B9); [lia | change (2 ^ 4) with 16; exact HR16 | lia].
      + apply (c1_af _ _ SHADOW_OFF _ _ _ B23); [lia | reflexivity | lia]. }
  pose proof (st_ok_pin_lit rsegs _ _ _ (25%bv : bv 5) 0 HS eq_refl
    ltac:(cbn [ms_regs restrict mkst]; rewrite H25; reflexivity)) as HS1.
  clear HS. rename HS1 into HS.
  assert (SHOK : sh_ok rsegs EBx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 E E) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D1) with (Z_to_bv 64 W6B_D1).
  aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan C1_V.
  + (* the two windows lie in the stack window of the journal *)
    lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
    apply awr_ok_nil.
  + eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c2_kio | | | exact HG | ].
    * eapply (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs [] (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
    * intros a Ha Hz.
      exact (RPgCfgChanges.kept_run (c1_head_wr R) _ _ (w_H W) memc memc (ms_mem ms)
        (fun a _ _ => eq_refl) HFr ltac:(c1_kwr B9) a Ha Hz).
    * cbv beta. split; [|split].
      -- c1_reg HS (10%bv : bv 5). reflexivity.
      -- eapply (tl_val_at _ _ (w_H W) ms 0%nat _ 0xc8 8%N _ _ R _);
           [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
           | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite B24; f_equal; lia
           | cbn; lia | lia].
      -- eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 0xf8 8%N _ _ R _);
           [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
           | reflexivity | cbn; lia | lia].
- (* a byte m left *)
  cbn [fuzz_u8 fst snd].
  pose proof (byte_range mb) as Hmb.
  set (m := bv_unsigned mb) in *.
  set (n := Z.of_nat (length (mb :: r1))) in *.
  assert (Hn : n = Z.of_nat (length r1) + 1) by (subst n; cbn [length]; lia).
  assert (Hnb : 1 <= n /\ c + n <= 2 ^ 47 - 1).
  { split; [lia|]. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham. lia. }
  assert (Hcd : c + 1 <= R - 16384 \/ R + 0x138 <= c) by (pose proof (Hdis c ltac:(lia)) as Hd; lia).
  assert (Hm0 : val_mem rsegs (mrestrict (w_H W) memc) (c + 0) 1 m).
  { destruct (Hg 0%nat ltac:(cbn [length map]; lia)) as [Hv _]. exact Hv. }
  set (E := Ereg regs (c1_hx1 n m)).
  assert (B9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
  assert (B23 : bv_unsigned (ew E 23) = SHADOW_OFF)
    by exact (eb_U_reg regs _ 23 23%bv _ eq_refl H23 ltac:(unfold SHADOW_OFF; lia)).
  assert (B24 : bv_unsigned (ew E 24) = c) by exact (eb_U_reg regs _ 24 24%bv c eq_refl H24 ltac:(lia)).
  assert (B25 : bv_unsigned (ew E 25) = n) by exact (eb_U_reg regs _ 25 25%bv n eq_refl H25 ltac:(lia)).
  assert (B14 : bv_unsigned (ew E 14) = c - 1) by exact (eb_U_reg regs _ 14 14%bv (c - 1) eq_refl H14 ltac:(lia)).
  assert (E32 : ew E 32 = Z_to_bv 64 (n + 1)) by exact (ew_Ereg_extra regs (c1_hx1 n m) 0).
  assert (E33 : ew E 33 = Z_to_bv 64 m) by exact (ew_Ereg_extra regs (c1_hx1 n m) 1).
  assert (B32 : bv_unsigned (ew E 32) = n + 1) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (B33 : bv_unsigned (ew E 33) = m) by (rewrite E33; apply unsigned_lit_small; lia).
  assert (HS : st_ok rsegs E c1_hss1 (restrict (w_H W) (mkst regs (Z_to_bv 64 W6B_D1) memc (seg_rom rsegs)))).
  { rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
    - apply regs_ok_Ereg.
    - vm_compute. reflexivity.
    - constructor; [|constructor; [|constructor; [|constructor]]].
      + unfold region_ok, c1_rB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        change (Ereg regs (c1_hx1 n m)) with E. rewrite B9. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable rsegs). apply Pw. lia.
      + unfold region_ok, c1_rC. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        change (Ereg regs (c1_hx1 n m)) with E. rewrite B9. split; [lia|]. split; [lia|].
        split; [intros o Ho; apply (apresent_writable rsegs); apply Pw; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ R 0xf8 8 (SOff 32 0) (n + 1));
          [cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Vf8].
      + unfold region_ok, c1_rI. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
        change (Ereg regs (c1_hx1 n m)) with E. rewrite B24. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val rsegs _ _ c 0 1 (SOff 33 0) m);
          [cbn [sv_denot]; rewrite B33, Z.add_0_r; reflexivity | change (8 * Z.of_N 1) with 8; lia | lia | exact Hm0].
    - apply pairwise_disjoint_of_extents. unfold c1_rB, c1_rC, c1_rI. cbn [map]. unfold extent_of_region.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      change (Ereg regs (c1_hx1 n m)) with E. rewrite B9, B24.
      repeat split; first [exact I | lia].
    - unfold facts_ok. cbn [c1_hf1 c1_fR c1_fK f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
      change (Ereg regs (c1_hx1 n m)) with E.
      split; [|split; exact I]. split; [|split; [|split; [|split; [|split; [|exact I]]]]].
      + apply (c1_af _ _ R _ _ _ B9); [lia | change (2 ^ 4) with 16; exact HR16 | lia].
      + apply (c1_af _ _ SHADOW_OFF _ _ _ B23); [lia | reflexivity | lia].
      + apply (c1_af _ _ c _ _ _ B24); [lia | apply Z.mod_1_r | lia].
      + apply (c1_af _ _ n _ _ _ B25); [lia | apply Z.mod_1_r | lia].
      + apply (c1_af _ _ m _ _ _ B33); [lia | apply Z.mod_1_r | lia]. }
  assert (SHOK : sh_ok rsegs EBx [] E (mrestrict (w_H W) memc)) by constructor.
  assert (HAE : env_agree 32 E E) by apply env_agree_refl.
  unfold cfg_at. change (w64 W6B_D1) with (Z_to_bv 64 W6B_D1).
  aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan C1_V.
  + (* the check of s8: the input byte is addressable *)
    apply (obl_of_range rsegs (w_H W) memc _ EBx _ _ c n Hrain).
    * apply (U_atom _ 23 SHADOW_OFF); [apply bv_eq; rewrite B23, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity
        | unfold SHADOW_OFF; lia].
    * rewrite (U_atom _ 24 c) by (try (apply bv_eq; rewrite B24, unsigned_lit_small by lia; reflexivity); lia). lia.
    * rewrite (U_atom _ 24 c) by (try (apply bv_eq; rewrite B24, unsigned_lit_small by lia; reflexivity); lia). lia.
  + lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp ?fp ?b0 ?bc ?lyx ?ow =>
      let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp fp b0 bc lyx ow) end.
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (R - sp0));
      [reflexivity | rewrite B9; lia | cbn [YP09.r_wlo YP09.r_whi]; lia | cbn [YP09.r_wlo YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
  + eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c2_kio | | | exact HG | ].
    * eapply (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs (c1_hx1 n m) (w_H W) _ HS);
        [env_agree_chain HAE | vm_compute; reflexivity].
    * intros a Ha Hz.
      exact (RPgCfgChanges.kept_run (c1_head_wr R) _ _ (w_H W) memc memc (ms_mem ms)
        (fun a _ _ => eq_refl) HFr ltac:(c1_kwr B9) a Ha Hz).
    * cbv beta. split; [|split].
      -- rewrite (st_ok_restrict_reg rsegs (w_H W) _ _ ms 10%bv HS).
         lazymatch type of HS with st_ok _ _ ?ssf _ =>
           replace (sr_get (ss_regs ssf) (10%bv : bv 5)) with c1_a0 by (vm_compute; reflexivity) end.
         unfold w64. apply c1_a0_val; [rewrite ?ew_ewset_other by lia; exact E33 | exact Hmb].
      -- eapply (tl_val_at _ _ (w_H W) ms 0%nat _ 0xc8 8%N _ _ R _);
           [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
           | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite B14; f_equal; lia
           | cbn; lia | lia].
      -- eapply (tl_val_at _ _ (w_H W) ms 1%nat _ 0xf8 8%N _ _ R _);
           [exact HS | reflexivity | c1_in | cbn [YP09.r_base base_val]; rewrite ?ew_ewset_other by lia; exact B9
           | cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite B32; f_equal; lia
           | cbn; lia | lia].
Qed.

(* ======================================== c1_vcell: 0x81284 .. 0x41ac8 ======================================== *)
Definition c1_rV : YP09.region := YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition c1_vf : facts := mkFacts [(10%nat, mkAF 0x9a500 0x9a540 3); c1_fK] [] [].
Definition c1_vss : sstate := mkSS C1_V sr_atoms [c1_rV] None c1_vf.

Lemma c1_vcell : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) i,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 10 = w64 (W6B_VOCAB + 8 * i) -> 0 <= i < 9 -> getr regs 23 = w64 SHADOW_OFF ->
  range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF W6B_VOCAB 72 ->
  val_mem rsegs (mrestrict (w_H W) memc) (W6B_VOCAB + 8 * i) 8 (w6b_vptr i) ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 C1_V) memc (seg_rom rsegs)) mdc)
  (w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_STRLEN regs memc mdc [1; 10; 11; 27]%bv (fun _ => False)
   (fun regs2 _ => getr regs2 1 = w64 C1_SLR /\ getr regs2 10 = w64 (w6b_vptr i) /\ getr regs2 27 = w64 (w6b_vptr i))).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs i HJ H10 Hi H23 Hra Hval.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
pose proof (c1_vptr_range i) as Hvp.
set (E := Ereg regs [Z_to_bv 64 (w6b_vptr i)]).
assert (B10 : bv_unsigned (ew E 10) = W6B_VOCAB + 8 * i)
  by exact (eb_U_reg regs _ 10 10%bv _ eq_refl H10 ltac:(unfold W6B_VOCAB; lia)).
assert (B23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by exact (eb_U_reg regs _ 23 23%bv _ eq_refl H23 ltac:(unfold SHADOW_OFF; lia)).
assert (E32 : ew E 32 = Z_to_bv 64 (w6b_vptr i)) by exact (ew_Ereg_extra regs [Z_to_bv 64 (w6b_vptr i)] 0).
assert (B32 : bv_unsigned (ew E 32) = w6b_vptr i) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E c1_vss (restrict (w_H W) (mkst regs (Z_to_bv 64 C1_V) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, c1_rV. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (Ereg regs [Z_to_bv 64 (w6b_vptr i)]) with E. rewrite B10.
    split; [unfold W6B_VOCAB; lia|]. split; [unfold W6B_VOCAB; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ _ 0 8 (SOff 32 0) (w6b_vptr i));
      [cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia |].
    rewrite Z.add_0_r. exact Hval.
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [c1_vf c1_fK f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    change (Ereg regs [Z_to_bv 64 (w6b_vptr i)]) with E.
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c1_af _ _ _ _ _ _ B10); [unfold W6B_VOCAB; lia | | lia].
      change (2 ^ 3) with 8. replace (W6B_VOCAB + 8 * i) with ((0x134a0 + i) * 8) by (unfold W6B_VOCAB; lia).
      apply Z.mod_mul. lia.
    + apply (c1_af _ _ SHADOW_OFF _ _ _ B23); [lia | reflexivity | lia]. }
assert (SHOK : sh_ok rsegs EBx [] E (mrestrict (w_H W) memc)) by constructor.
assert (HAE : env_agree 32 E E) by apply env_agree_refl.
aj_run_to_tok eb_tbl_ok HS HJ SHOK Espan W7_STRLEN.
- (* the check of the cell: the table's 72 bytes are addressable *)
  apply (obl_of_range rsegs (w_H W) memc _ EBx _ _ W6B_VOCAB 72 Hra).
  + apply (U_atom _ 23 SHADOW_OFF); [apply bv_eq; rewrite B23, unsigned_lit_small by (unfold SHADOW_OFF; lia); reflexivity
      | unfold SHADOW_OFF; lia].
  + rewrite (U_atom _ 10 (W6B_VOCAB + 8 * i)) by (try (apply bv_eq; rewrite B10, unsigned_lit_small by (unfold W6B_VOCAB; lia);
      reflexivity); unfold W6B_VOCAB; lia). lia.
  + rewrite (U_atom _ 10 (W6B_VOCAB + 8 * i)) by (try (apply bv_eq; rewrite B10, unsigned_lit_small by (unfold W6B_VOCAB; lia);
      reflexivity); unfold W6B_VOCAB; lia). lia.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c2_kio | | | exact HG | ].
  + eapply (RPgSteps.regs_kept_of_st_ok rsegs _ _ ms regs [Z_to_bv 64 (w6b_vptr i)] (w_H W) _ HS);
      [env_agree_chain HAE | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (RPgCfgChanges.kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr ltac:(c1_kwr B10) a Ha Hz).
  + cbv beta. split; [|split].
    * c1_reg HS (1%bv : bv 5). reflexivity.
    * c1_reg HS (10%bv : bv 5). cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite B32, Z.add_0_r. reflexivity.
    * c1_reg HS (27%bv : bv 5). cbn [sv_denot]. rewrite ?ew_ewset_other by lia. rewrite B32, Z.add_0_r. reflexivity.
Qed.

(* ======================================== c1_set: 0x812a4 .. 0x510d4 ======================================== *)
Definition c1_rM : YP09.region := YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0xc0 0xc0 [YP09.mkChunk 0xc0 (CVal 8 (SOff 32 0))].
Definition c1_mss : sstate := mkSS C1_SLR sr_atoms [c1_rM] None (mkFacts [c1_fR; (10%nat, mkAF 12 18 0)] [] []).

Lemma c1_set : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) R F n,
  ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  getr regs 9 = w64 R -> 0x7fff7f800000 <= R -> R + 0x1a0 <= 2 ^ 47 -> R mod 16 = 0 ->
  getr regs 10 = w64 n -> 12 <= n <= 18 ->
  val_mem rsegs (mrestrict (w_H W) memc) (R + 0xc0) 8 (F + 0xf8) -> 0 <= F + 0xf8 < 2 ^ 64 ->
  SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 C1_SLR) memc (seg_rom rsegs)) mdc)
  (w7_post B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k W7_MEMCPY regs memc mdc [1; 10; 11; 12; 21; 24; 25]%bv (fun _ => False)
   (fun regs2 _ => getr regs2 1 = w64 C1_MCR /\ getr regs2 10 = w64 (F + 0xf8) /\ getr regs2 11 = getr regs 27 /\
     getr regs2 12 = w64 n /\ getr regs2 21 = w64 n /\ getr regs2 24 = w64 (F + 0xf8) /\ getr regs2 25 = w64 n)).
Proof using LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R F n HJ H9 HR1 HR2 HR3 H10 Hn Hval HFv.
pose proof RPgCfgChanges.cfg_wx as Hwx. pose proof RPgCfgChanges.cfg_segs_low as Hsegs.
set (E := Ereg regs [Z_to_bv 64 (F + 0xf8)]).
assert (B9 : bv_unsigned (ew E 9) = R) by exact (eb_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia)).
assert (B10 : bv_unsigned (ew E 10) = n) by exact (eb_U_reg regs _ 10 10%bv n eq_refl H10 ltac:(lia)).
assert (E32 : ew E 32 = Z_to_bv 64 (F + 0xf8)) by exact (ew_Ereg_extra regs [Z_to_bv 64 (F + 0xf8)] 0).
assert (B32 : bv_unsigned (ew E 32) = F + 0xf8) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E c1_mss (restrict (w_H W) (mkst regs (Z_to_bv 64 C1_SLR) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
  - apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor].
    unfold region_ok, c1_rM. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    change (Ereg regs [Z_to_bv 64 (F + 0xf8)]) with E. rewrite B9.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val rsegs _ _ _ 0xc0 8 (SOff 32 0) (F + 0xf8));
      [cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity | change (8 * Z.of_N 8) with 64; lia | lia | exact Hval].
  - cbn [pairwise_disjoint all_disjoint]. tauto.
  - unfold facts_ok. cbn [c1_mss c1_fR f_atoms f_conds f_alias atoms_ok conds_ok alias_ok ss_facts].
    change (Ereg regs [Z_to_bv 64 (F + 0xf8)]) with E.
    split; [|split; exact I]. split; [|split; [|exact I]].
    + apply (c1_af _ _ R _ _ _ B9); [lia | change (2 ^ 4) with 16; exact HR3 | lia].
    + apply (c1_af _ _ n _ _ _ B10); [lia | apply Z.mod_1_r | lia]. }
aj_run_to eb_tbl_ok HS HJ W7_MEMCPY.
- awr_ok_tac.
- eapply (w7_post_of_run B); [exact HS | reflexivity | reflexivity | exact HJ | c2_kio | | | exact HG | ].
  + eapply (w7_regs_kept _ _ ms regs [Z_to_bv 64 (F + 0xf8)] (w_H W) _ HS); [apply env_agree_refl | vm_compute; reflexivity].
  + intros a Ha Hz.
    exact (RPgCfgChanges.kept_run (fun _ => False) _ _ (w_H W) memc memc (ms_mem ms)
      (fun a _ _ => eq_refl) HFr ltac:(c1_kwr B9) a Ha Hz).
  + cbv beta.
    split; [c1_reg HS (1%bv : bv 5); reflexivity|].
    split; [c1_reg HS (10%bv : bv 5); cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity|].
    split; [c1_reg HS (11%bv : bv 5); exact (tl_atom regs _ 27 27%bv eq_refl)|].
    split; [c1_reg HS (12%bv : bv 5); exact (eq_trans (tl_atom regs _ 10 10%bv eq_refl) H10)|].
    split; [c1_reg HS (21%bv : bv 5); exact (eq_trans (tl_atom regs _ 10 10%bv eq_refl) H10)|].
    split; [c1_reg HS (24%bv : bv 5); cbn [sv_denot]; rewrite B32, Z.add_0_r; reflexivity|].
    c1_reg HS (25%bv : bv 5). exact (eq_trans (tl_atom regs _ 10 10%bv eq_refl) H10).
Qed.
End d.
End b.

Print Assumptions c1_head.
Print Assumptions c1_vcell.
Print Assumptions c1_set.
