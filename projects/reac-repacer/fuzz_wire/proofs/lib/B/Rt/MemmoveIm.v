(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap's v1.9.0 asan-ubsan build: the twin of
   lib/A/Rt/MemmoveIm.v (the same proof; its addresses moved from the asan build to the asan-ubsan build by function pairing). *)
(* Modified by Theorem Labs, 2026-10: relocated to reac-repacer/fuzz_wire's asan-ubsan build: addresses and numbers moved by symbol to its asan-ubsan image; module paths changed. *)
(* __sanitizer::internal_memmove (0x63078, 88 B, leaf, no stack frame): the byte loops that __asan_memmove
   (0x510b0) tail-calls at 0x51190.  Unlike internal_memcpy (cgif YB14.v, YE08.cpyH) the source and the
   destination MAY overlap: the forward loop runs when dst < src, the backward loop when src < dst, and
   dst = src returns at once.  The loop lemmas therefore replace cpyH's disjointness premise by the
   direction premise that makes each loop read source bytes it has not yet overwritten. *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YE08 YE21.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition W_mm00 : bv 32 := 0x02b57463.
Lemma D_mm00 : decode_any W_mm00 = Some (Branch BC_GEU 10 11 40, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm04 : bv 32 := 0x04c05863.
Lemma D_mm04 : decode_any W_mm04 = Some (Branch BC_GE 0 12 80, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm08 : bv 32 := 0x00c50633.
Lemma D_mm08 : decode_any W_mm08 = Some (Op ALU_ADD 12 10 12, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm0c : bv 32 := 0x00050693.
Lemma D_mm0c : decode_any W_mm0c = Some (OpImm ALU_ADD 13 10 0, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm10 : bv 32 := 0x0005c703.
Lemma D_mm10 : decode_any W_mm10 = Some (Load SZ1 false 14 11 0, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm14 : bv 32 := 0x00e68023.
Lemma D_mm14 : decode_any W_mm14 = Some (Store SZ1 13 14 0, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm18 : bv 32 := 0x00168693.
Lemma D_mm18 : decode_any W_mm18 = Some (OpImm ALU_ADD 13 13 1, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm1c : bv 32 := 0x00158593.
Lemma D_mm1c : decode_any W_mm1c = Some (OpImm ALU_ADD 11 11 1, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm20 : bv 32 := 0xfec698e3.
Lemma D_mm20 : decode_any W_mm20 = Some (Branch BC_NE 13 12 8176, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm24 : bv 32 := 0x0300006f.
Lemma D_mm24 : decode_any W_mm24 = Some (Jal 0 48, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm28 : bv 32 := 0x02a5f663.
Lemma D_mm28 : decode_any W_mm28 = Some (Branch BC_GEU 11 10 44, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm2c : bv 32 := 0x02c05463.
Lemma D_mm2c : decode_any W_mm2c = Some (Branch BC_GE 0 12 40, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm30 : bv 32 := 0xfff60693.
Lemma D_mm30 : decode_any W_mm30 = Some (OpImm ALU_ADD 13 12 4095, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm34 : bv 32 := 0x00100613.
Lemma D_mm34 : decode_any W_mm34 = Some (OpImm ALU_ADD 12 0 1, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm38 : bv 32 := 0x00d58733.
Lemma D_mm38 : decode_any W_mm38 = Some (Op ALU_ADD 14 11 13, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm3c : bv 32 := 0x00074703.
Lemma D_mm3c : decode_any W_mm3c = Some (Load SZ1 false 14 14 0, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm40 : bv 32 := 0x00d507b3.
Lemma D_mm40 : decode_any W_mm40 = Some (Op ALU_ADD 15 10 13, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm44 : bv 32 := 0x00168813.
Lemma D_mm44 : decode_any W_mm44 = Some (OpImm ALU_ADD 16 13 1, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm48 : bv 32 := 0xfff68693.
Lemma D_mm48 : decode_any W_mm48 = Some (OpImm ALU_ADD 13 13 4095, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm4c : bv 32 := 0x00e78023.
Lemma D_mm4c : decode_any W_mm4c = Some (Store SZ1 15 14 0, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm50 : bv 32 := 0xff0664e3.
Lemma D_mm50 : decode_any W_mm50 = Some (Branch BC_LTU 12 16 8168, 4%Z). Proof. vm_refl_bv. Qed.
Definition W_mm54 : bv 32 := 0x00008067.
Lemma D_mm54 : decode_any W_mm54 = Some (Jalr 0 1 0, 4%Z). Proof. vm_refl_bv. Qed.
Definition immove_words : list (bv 32) :=
[W_mm00; W_mm04; W_mm08; W_mm0c; W_mm10; W_mm14; W_mm18; W_mm1c; W_mm20; W_mm24; W_mm28;
W_mm2c; W_mm30; W_mm34; W_mm38; W_mm3c; W_mm40; W_mm44; W_mm48; W_mm4c; W_mm50; W_mm54].
Definition immove_clob : list reg := [11; 12; 13; 14; 15; 16].
(* wbytes facts for an overlapping copy: the backward loop extends its written block downwards. *)
Lemma wb_inside : forall bs m (a x : word),
(bv_unsigned a + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
(bv_unsigned a <= bv_unsigned x < bv_unsigned a + Z.of_nat (length bs))%Z ->
wbytes m a bs x = nth_error bs (Z.to_nat (bv_unsigned x - bv_unsigned a)).
Proof.
induction bs as [|b rest IH]; intros m a x Hnw Hx; [cbn [length] in Hx; lia|].
cbn [length] in Hnw, Hx. cbn [wbytes].
destruct rest as [|b' rest'].
{ cbn [wbytes length] in *. assert (Heq : bv_unsigned x = bv_unsigned a) by lia.
rewrite Heq, Z.sub_diag. replace x with a by (apply bv_eq; lia). rewrite bv_eqb_refl. reflexivity. }
cbn [length] in Hnw, Hx.
assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; lia).
destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned a)) as [Heq|Hne].
- rewrite (wbytes_below (b' :: rest') _ (a + 1) x); [| cbn [length]; rewrite Hu1; lia | rewrite Hu1; lia].
rewrite Heq, Z.sub_diag. replace x with a by (apply bv_eq; lia). rewrite bv_eqb_refl. reflexivity.
- rewrite (IH _ (a + 1)%bv x) by (cbn [length]; rewrite Hu1; lia). rewrite Hu1.
replace (Z.to_nat (bv_unsigned x - bv_unsigned a)) with (S (Z.to_nat (bv_unsigned x - (bv_unsigned a + 1)))) by lia.
reflexivity.
Qed.
Lemma wb_cong : forall (l : list byte) (m m' : word -> option byte) (a x : word),
(bv_unsigned a + Z.of_nat (length l) <= 2 ^ 64)%Z -> m x = m' x ->
wbytes m a l x = wbytes m' a l x.
Proof.
intros l m m' a x Hnw Hx.
destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a)) as [L|L].
- rewrite !wbytes_below by lia. exact Hx.
- destruct (Z_lt_le_dec (bv_unsigned x) (bv_unsigned a + Z.of_nat (length l))) as [I|I].
+ rewrite !wb_inside by lia. reflexivity.
+ rewrite !wbytes_above by lia. exact Hx.
Qed.
Lemma wbytes_one : forall (m : word -> option byte) (a : word) (b : byte),
wbytes m a [b] = (fun z => if bv_eqb z a then Some b else m z).
Proof. reflexivity. Qed.
Lemma wbytes_cons_eq : forall (m : word -> option byte) (a : word) (b : byte) l,
wbytes m a (b :: l) = wbytes (fun z => if bv_eqb z a then Some b else m z) (a + 1) l.
Proof. reflexivity. Qed.
Lemma wb_push_front : forall (l : list byte) (m : word -> option byte) (a : word) (b : byte),
(bv_unsigned a + 1 + Z.of_nat (length l) <= 2 ^ 64)%Z ->
wbytes (wbytes m (a + 1) l) a [b] = wbytes m a (b :: l).
Proof.
intros l m a b Hnw. destruct l as [|c l]; [reflexivity|].
assert (Hu1 : bv_unsigned (a + 1) = (bv_unsigned a + 1)%Z) by (apply u_add1; cbn [length] in Hnw; lia).
rewrite (wbytes_one (wbytes m (a + 1) (c :: l)) a b), (wbytes_cons_eq m a b (c :: l)).
apply functional_extensionality. intros z.
destruct (bv_eqb z a) eqn:Ez.
- apply Fs.bv_eqb_eq in Ez. subst z.
rewrite (wbytes_below (c :: l) _ (a + 1) a) by (rewrite Hu1; lia).
rewrite bv_eqb_refl. reflexivity.
- apply wb_cong; [rewrite Hu1; lia|]. rewrite Ez. reflexivity.
Qed.
Lemma at_at1 : forall (d : word) i,
(0 <= i)%Z -> (bv_unsigned d + i + 1 < 2 ^ 64)%Z -> (at_ d i + 1)%bv = at_ d (i + 1).
Proof.
intros d i Hi Hd. pose proof (u64_range d) as Hr.
assert (Hu : bv_unsigned (at_ d i) = (bv_unsigned d + i)%Z) by (apply at_u; lia).
apply bv_eq. rewrite u_add1 by lia. rewrite Hu. rewrite at_u by lia. lia.
Qed.
Lemma sig_small : forall z, (0 <= z < 2 ^ 62)%Z -> bv_signed (Z_to_bv 64 z) = z.
Proof.
intros z Hz. rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap.
change (bv_modulus 64) with (2 ^ 64)%Z. change (bv_half_modulus 64) with (2 ^ 63)%Z.
rewrite Z.mod_small by lia. lia.
Qed.
Ltac condzs :=
rwH; unfold c_lts, bv_lts; rewrite ?sig_small by lia;
first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Lemma addi_lit_p : forall z k, (0 <= k)%Z -> (0 <= z)%Z -> (z + k < 2 ^ 64)%Z ->
v_addi (Z_to_bv 64 z) k = Z_to_bv 64 (z + k).
Proof. intros z k Hk Hz Hzk. rewrite v_addi_nneg_t by (rewrite ?u_Z2bv by lia; lia). rewrite u_Z2bv by lia. reflexivity. Qed.
Lemma addi_lit_m1 : forall z, (1 <= z < 2 ^ 64)%Z -> v_addi (Z_to_bv 64 z) (-1) = Z_to_bv 64 (z - 1).
Proof. intros z Hz. rewrite v_addi_m1 by (rewrite ?u_Z2bv by lia; lia). rewrite u_Z2bv by lia. reflexivity. Qed.
Ltac condu :=
rwH; unfold c_ltu, bv_ltu; rewrite ?u_Z2bv by lia;
first [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Section b.
Variable segs : list Segment.
Variable base : word.
Variable rom : word -> option byte.
Hypothesis HCODE : code_at segs base 0 immove_words.
#[local] Abbreviation CL := (fun r => In r immove_clob).
Ltac get_code :=
let HC := fresh "HC" in
pose proof HCODE as HC; cbn [code_at immove_words Z.add Pos.add Pos.succ] in HC;
destruct HC as (C00 & C04 & C08 & C0c & C10 & C14 & C18 & C1c & C20 & C24 & C28 &
C2c & C30 & C34 & C38 & C3c & C40 & C44 & C48 & C4c & C50 & C54 & _).
Theorem immove_eq_run : forall mem (p : word) k regs (ret : word),
ret_ok ret -> getr regs 1 = ret -> getr regs 10 = p -> getr regs 11 = p -> getr regs 12 = k ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem rom) (mkst regs' ret mem rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. intros mem p k regs ret Hret H1 H10 H11 H12.
eexists. split.
- ab_tk C00 D_mm00 ltac:(condz).
ab_tk C28 D_mm28 ltac:(condz).
aret C54 D_mm54 ret.
apply mst_refl.
- apply regs_agree_refl.
Qed.
Section c.
Variable mem0 : word -> option byte.
Variables dst src : word.
Variable n : Z.
Variable bs : list byte.
Hypothesis Hn : (0 <= n < 2 ^ 62)%Z.
Hypothesis Hlen : length bs = Z.to_nat n.
Hypothesis Hsrc : rdn segs mem0 src (length bs) = Some bs.
Hypothesis Hdst : store_ok segs mem0 dst (length bs) = true.
Hypothesis Hnws : (bv_unsigned src + n < 2 ^ 64)%Z.
Hypothesis Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z.
Definition MK (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
Definition NB (k : Z) : word -> option byte := wbytes mem0 (at_ dst (n - k)) (skipn (Z.to_nat (n - k)) bs).
Definition B_ (j : Z) : byte := b_ bs j.
Lemma SOK : forall j k, (0 <= j)%Z -> (j + Z.of_nat k <= n)%Z -> store_ok segs mem0 (at_ dst j) k = true.
Proof.
intros j k Hj Hk.
exact (store_ok_at segs mem0 dst (length bs) [] j k ltac:(rewrite Hlen; lia) Hdst Hj ltac:(rewrite Hlen; lia)).
Qed.
Lemma RD1 : forall j, (0 <= j)%Z -> (j + 1 <= n)%Z -> rdn segs mem0 (at_ src j) 1 = Some [B_ j].
Proof.
intros j Hj H1. unfold B_.
replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
rewrite (rdn_sub segs mem0 (length bs) src bs (Z.to_nat j) 1 Hsrc) by (rewrite Hlen; lia).
rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
Qed.
Lemma MK_full : MK n = wbytes mem0 dst bs.
Proof. unfold MK. rewrite firstn_all2 by lia. reflexivity. Qed.
Lemma NB_full : NB n = wbytes mem0 dst bs.
Proof. unfold NB. rewrite Z.sub_diag. cbn [Z.to_nat]. rewrite skipn_O, at_0. reflexivity. Qed.
Lemma NB_0 : NB 0 = mem0.
Proof. unfold NB. rewrite Z.sub_0_r, skipn_all2 by lia. reflexivity. Qed.
Lemma bs_nil : n = 0%Z -> bs = [].
Proof. intros ->. apply length_zero_iff_nil. rewrite Hlen. reflexivity. Qed.
(* forward loop: dst < src *)
Section F.
Hypothesis Hlt : (bv_unsigned dst < bv_unsigned src)%Z.
Lemma f_rd : forall k j, (0 <= k <= j)%Z -> (j + 1 <= n)%Z -> rdn segs (MK k) (at_ src j) 1 = Some [B_ j].
Proof.
intros k j Hk Hj. pose proof (u64_range src) as Hsr. pose proof (u64_range dst) as Hdr.
unfold MK. rewrite rdn_wbytes_disjoint.
- apply RD1; lia.
- rewrite length_firstn, Hlen, at_u by lia. lia.
- rewrite at_u by lia. lia.
Qed.
Lemma f_sok : forall k j, (0 <= j)%Z -> (j + 1 <= n)%Z -> store_ok segs (MK k) (at_ dst j) 1 = true.
Proof. intros k j Hj H1. unfold MK. eapply store_ok_mono; [apply wbytes_grows|]. apply SOK; cbn; lia. Qed.
Lemma f_ext : forall k, (0 <= k)%Z -> (k + 1 <= n)%Z -> wbytes (MK k) (at_ dst k) [B_ k] = MK (k + 1).
Proof.
intros k Hk H1. unfold MK, B_, b_.
replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
rewrite <- sub_nth by (rewrite Hlen; lia).
rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
Qed.
Lemma f_lbu : forall regs pc w rd rs (imm : bv 12) k j0 j,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
(0 <= k <= j)%Z -> (j + 1 <= n)%Z ->
RiscvSemantics.step segs (mkst regs pc (MK k) rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (B_ j)))) (v_addi pc 4) (MK k) rom).
Proof.
intros regs pc w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj1.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hj. apply f_rd; lia.
Qed.
Lemma f_sb : forall regs pc w rs1 rs2 (imm : bv 12) k k0 (v : word),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
getr regs rs1 = at_ dst k0 -> (k0 + bv_signed imm = k)%Z ->
getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = B_ k ->
(0 <= k)%Z -> (k + 1 <= n)%Z ->
RiscvSemantics.step segs (mkst regs pc (MK k) rom) =
MachineOk (mkst regs (v_addi pc 4) (MK (k + 1)) rom).
Proof.
intros regs pc w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
rewrite <- (f_ext k) by lia.
eapply YK0v.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
- rewrite Hrs1, at_addi, Hk. reflexivity.
- apply f_sok; lia.
Qed.
Ltac flbu F D jj :=
chain_step; [reflexivity
| eapply f_lbu with (j := jj);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia]
| step_simpl]; vn.
Ltac fsb F D kk :=
chain_step; [reflexivity
| eapply f_sb with (k := kk);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | apply sb_val_b | lia | lia]
| step_simpl]; vn.
Lemma f_loop : forall (i : nat) regs (ret : word) k,
ret_ok ret -> getr regs 1 = ret ->
getr regs 11 = at_ src k -> getr regs 13 = at_ dst k -> getr regs 12 = at_ dst n ->
(0 <= k < n)%Z -> Z.of_nat i = (n - 1 - k)%Z ->
exists regs',
msteps segs (mkst regs (at_ base 16) (MK k) rom) (mkst regs' ret (MK n) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
induction i as [|i IH]; intros regs ret k Hret H1 H11 H13 H12 Hk Hi.
-
eexists. split.
+ flbu C10 D_mm10 k.
fsb C14 D_mm14 k.
an C18 D_mm18.
an C1c D_mm1c.
ab_ft C20 D_mm20 ltac:(condz).
an C24 D_mm24.
aret C54 D_mm54 ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold immove_clob. solve_regs_agree.
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 16) (MK (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src (k + 1) /\ getr r 13 = at_ dst (k + 1)
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* flbu C10 D_mm10 k.
fsb C14 D_mm14 k.
an C18 D_mm18.
an C1c D_mm1c.
ab_tk C20 D_mm20 ltac:(condz).
apply mst_refl.
* post. unfold immove_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Theorem immove_fwd_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
rewrite <- MK_full. change mem0 with (MK 0) at 1.
destruct (Z.eq_dec n 0) as [Hz|Hnz].
-
eexists. split.
+ ab_ft C00 D_mm00 ltac:(condz).
ab_tk C04 D_mm04 ltac:(condzs).
aret C54 D_mm54 ret.
rewrite Hz. apply mst_refl.
+ apply regs_agree_refl.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 16) (MK 0) rom)
(fun r => getr r 1 = ret /\ getr r 11 = at_ src 0 /\ getr r 13 = at_ dst 0
/\ getr r 12 = at_ dst n /\ regs_agree CL regs r)).
+ eexists. split.
* ab_ft C00 D_mm00 ltac:(condz).
ab_ft C04 D_mm04 ltac:(condzs).
av C08 D_mm08 (at_ dst n) ltac:(apply v_add_at; lia).
an C0c D_mm0c.
apply mst_refl.
* post; rewrite ?at_0; try reflexivity. unfold immove_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R11 & R13 & R12 & AG).
destruct (f_loop (Z.to_nat (n - 1)) r1 ret 0 Hret R1 R11 R13 R12 ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End F.
(* backward loop: src < dst *)
Section Bw.
Hypothesis Hgt : (bv_unsigned src < bv_unsigned dst)%Z.
Lemma b_rd : forall k i, (0 <= k)%Z -> (k + 1 <= n)%Z -> i = (n - 1 - k)%Z ->
rdn segs (NB k) (at_ src i) 1 = Some [B_ i].
Proof.
intros k i Hk H1 Hi. pose proof (u64_range src) as Hsr. pose proof (u64_range dst) as Hdr.
unfold NB. rewrite rdn_wbytes_below.
- apply RD1; lia.
- rewrite at_u, at_u by lia. lia.
- rewrite length_skipn, Hlen, at_u by lia. lia.
Qed.
Lemma b_sok : forall k i, (0 <= i)%Z -> (i + 1 <= n)%Z -> store_ok segs (NB k) (at_ dst i) 1 = true.
Proof. intros k i Hi H1. unfold NB. eapply store_ok_mono; [apply wbytes_grows|]. apply SOK; cbn; lia. Qed.
Lemma b_ext : forall k i, (0 <= k)%Z -> (k + 1 <= n)%Z -> i = (n - 1 - k)%Z ->
wbytes (NB k) (at_ dst i) [B_ i] = NB (k + 1).
Proof.
intros k i Hk H1 Hi. pose proof (u64_range src) as Hsr. pose proof (u64_range dst) as Hdr.
unfold NB, B_, b_.
replace (n - k)%Z with (i + 1)%Z by lia. replace (n - (k + 1))%Z with i by lia.
rewrite <- (at_at1 dst i) by lia.
rewrite wb_push_front by (rewrite length_skipn, Hlen, at_u by lia; lia).
f_equal.
rewrite (skipn_nth bs (Z.to_nat i) (Z_to_bv 8 0)) by (rewrite Hlen; lia).
replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity.
Qed.
Lemma b_lbu : forall regs pc w rd rs (imm : bv 12) k i,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
getr regs rs = at_ src i -> (bv_signed imm = 0)%Z ->
(0 <= k)%Z -> (k + 1 <= n)%Z -> i = (n - 1 - k)%Z ->
RiscvSemantics.step segs (mkst regs pc (NB k) rom) =
MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (Z_to_bv 64 (bv_unsigned (B_ i)))) (v_addi pc 4) (NB k) rom).
Proof.
intros regs pc w rd rs imm k i Hf He Hd Hrs Hi0 Hk H1 Hi.
eapply step_lbu; [exact Hf | exact He | exact Hd |].
rewrite Hrs, at_addi, Hi0, Z.add_0_r. apply (b_rd k i); lia.
Qed.
Lemma b_sb : forall regs pc w rs1 rs2 (imm : bv 12) k i (v : word),
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
getr regs rs1 = at_ dst i -> (bv_signed imm = 0)%Z ->
getr regs rs2 = v -> Z_to_bv 8 (bv_unsigned v) = B_ i ->
(0 <= k)%Z -> (k + 1 <= n)%Z -> i = (n - 1 - k)%Z ->
RiscvSemantics.step segs (mkst regs pc (NB k) rom) =
MachineOk (mkst regs (v_addi pc 4) (NB (k + 1)) rom).
Proof.
intros regs pc w rs1 rs2 imm k i v Hf He Hd Hrs1 Hi0 Hrs2 Hb Hk H1 Hi.
rewrite <- (b_ext k i) by lia.
eapply YK0v.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
- rewrite Hrs1, at_addi, Hi0, Z.add_0_r. reflexivity.
- apply b_sok; lia.
Qed.
Ltac blbu F D ii :=
chain_step; [reflexivity
| eapply b_lbu with (i := ii);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia | lia]
| step_simpl]; vn.
Ltac bsb F D ii :=
chain_step; [reflexivity
| eapply b_sb with (i := ii);
[exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia
| gres; rwH; reflexivity | apply sb_val_b | lia | lia | lia]
| step_simpl]; vn.
Lemma b_loop : forall (q : nat) regs (ret : word) k i,
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src ->
getr regs 13 = Z_to_bv 64 i -> getr regs 12 = Z_to_bv 64 1 ->
(0 <= k)%Z -> (k + 1 <= n)%Z -> i = (n - 1 - k)%Z -> Z.of_nat q = i ->
exists regs',
msteps segs (mkst regs (at_ base 56) (NB k) rom) (mkst regs' ret (NB n) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
induction q as [|q IH]; intros regs ret k i Hret H1 H10 H11 H13 H12 Hk Hkn Hi Hq.
-
eexists. split.
+ av C38 D_mm38 (at_ src i) ltac:(apply v_add_at; lia).
blbu C3c D_mm3c i.
av C40 D_mm40 (at_ dst i) ltac:(apply v_add_at; lia).
av C44 D_mm44 (Z_to_bv 64 (i + 1)) ltac:(apply addi_lit_p; lia).
an C48 D_mm48.
bsb C4c D_mm4c i.
ab_ft C50 D_mm50 ltac:(condu).
aret C54 D_mm54 ret.
replace (k + 1)%Z with n by lia. apply mst_refl.
+ unfold immove_clob. solve_regs_agree.
-
eapply (runs_trans segs _ (fun r => mkst r (at_ base 56) (NB (k + 1)) rom)
(fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src
/\ getr r 13 = Z_to_bv 64 (i - 1) /\ getr r 12 = Z_to_bv 64 1 /\ regs_agree CL regs r)).
+ eexists. split.
* av C38 D_mm38 (at_ src i) ltac:(apply v_add_at; lia).
blbu C3c D_mm3c i.
av C40 D_mm40 (at_ dst i) ltac:(apply v_add_at; lia).
av C44 D_mm44 (Z_to_bv 64 (i + 1)) ltac:(apply addi_lit_p; lia).
av C48 D_mm48 (Z_to_bv 64 (i - 1)) ltac:(apply addi_lit_m1; lia).
bsb C4c D_mm4c i.
ab_tk C50 D_mm50 ltac:(condu).
apply mst_refl.
* post.
unfold immove_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R10 & R11 & R13 & R12 & AG).
destruct (IH r1 ret (k + 1)%Z (i - 1)%Z Hret R1 R10 R11 R13 R12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
Theorem immove_bwd_run : forall regs (ret : word),
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree CL regs regs'.
Proof.
get_code. intros regs ret Hret H1 H10 H11 H12.
pose proof (u64_range src) as Hs. pose proof (u64_range dst) as Hd.
rewrite <- NB_full. rewrite <- NB_0.
destruct (Z.eq_dec n 0) as [Hz|Hnz].
-
eexists. split.
+ ab_tk C00 D_mm00 ltac:(condz).
ab_ft C28 D_mm28 ltac:(condz).
ab_tk C2c D_mm2c ltac:(condzs).
aret C54 D_mm54 ret.
rewrite Hz. apply mst_refl.
+ apply regs_agree_refl.
- eapply (runs_trans segs _ (fun r => mkst r (at_ base 56) (NB 0) rom)
(fun r => getr r 1 = ret /\ getr r 10 = dst /\ getr r 11 = src
/\ getr r 13 = Z_to_bv 64 (n - 1) /\ getr r 12 = Z_to_bv 64 1 /\ regs_agree CL regs r)).
+ eexists. split.
* ab_tk C00 D_mm00 ltac:(condz).
ab_ft C28 D_mm28 ltac:(condz).
ab_ft C2c D_mm2c ltac:(condzs).
av C30 D_mm30 (Z_to_bv 64 (n - 1)) ltac:(apply addi_lit_m1; lia).
av C34 D_mm34 (Z_to_bv 64 1) ltac:(apply v_addi_0_1).
apply mst_refl.
* post.
unfold immove_clob. solve_regs_agree.
+ cbv beta. intros r1 (R1 & R10 & R11 & R13 & R12 & AG).
destruct (b_loop (Z.to_nat (n - 1)) r1 ret 0 (n - 1)%Z Hret R1 R10 R11 R13 R12
ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (r2 & RUN & AG2).
exists r2. split; [exact RUN | eapply regs_agree_trans; eassumption].
Qed.
End Bw.
Theorem immove_ne_run : forall regs (ret : word),
(bv_unsigned dst < bv_unsigned src \/ bv_unsigned src < bv_unsigned dst)%Z ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps segs (mkst regs (at_ base 0) mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree CL regs regs'.
Proof.
intros regs ret [Hd|Hd] Hret H1 H10 H11 H12.
- exact (immove_fwd_run Hd regs ret Hret H1 H10 H11 H12).
- exact (immove_bwd_run Hd regs ret Hret H1 H10 H11 H12).
Qed.
End c.
End b.
End a.
From OSSVerify.reac_repacer.fuzz_wire.images Require Import AsanUbsan.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_immove_entry : word := 0x63078.
Lemma tfib_immove_code :
code_at AsanUbsan.M.loaded_segments tfib_immove_entry 0 immove_words.
Proof. unfold immove_words. code_at_vm. Qed.
Theorem tfib_immove : forall mem0 (dst src : word) n bs rom regs (ret : word),
(0 <= n < 2 ^ 62)%Z -> length bs = Z.to_nat n ->
rdn AsanUbsan.M.loaded_segments mem0 src (length bs) = Some bs ->
store_ok AsanUbsan.M.loaded_segments mem0 dst (length bs) = true ->
(bv_unsigned src + n < 2 ^ 64)%Z -> (bv_unsigned dst + n < 2 ^ 64)%Z ->
(bv_unsigned dst < bv_unsigned src \/ bv_unsigned src < bv_unsigned dst)%Z ->
ret_ok ret -> getr regs 1 = ret ->
getr regs 10 = dst -> getr regs 11 = src -> getr regs 12 = Z_to_bv 64 n ->
exists regs',
msteps AsanUbsan.M.loaded_segments
(mkst regs tfib_immove_entry mem0 rom) (mkst regs' ret (wbytes mem0 dst bs) rom)
/\ regs_agree (fun r => In r immove_clob) regs regs'.
Proof.
intros mem0 dst src n bs rom regs ret Hn Hlen Hsrc Hdst Hnws Hnwd Hdir Hret H1 H10 H11 H12.
rewrite <- (at_0 tfib_immove_entry).
apply (immove_ne_run _ _ rom tfib_immove_code mem0 dst src n bs Hn Hlen Hsrc Hdst Hnws Hnwd); assumption.
Qed.
Theorem tfib_immove_eq : forall mem (p : word) k rom regs (ret : word),
ret_ok ret -> getr regs 1 = ret -> getr regs 10 = p -> getr regs 11 = p -> getr regs 12 = k ->
exists regs',
msteps AsanUbsan.M.loaded_segments (mkst regs tfib_immove_entry mem rom) (mkst regs' ret mem rom)
/\ regs_agree (fun r => In r immove_clob) regs regs'.
Proof.
intros mem p k rom regs ret Hret H1 H10 H11 H12.
rewrite <- (at_0 tfib_immove_entry).
apply (immove_eq_run _ _ rom tfib_immove_code mem p k regs ret); assumption.
Qed.
End d.
