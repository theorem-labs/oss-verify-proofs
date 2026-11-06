(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0i.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YP0i.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK0o YK15.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP00 YP0k YP06 YP03.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition srl3_atom (v : sv) : option (nat * Z) :=
match v with
| SAlu ALU_SRL (SOff p c) (SLit k) => if k =? 3 then Some (p, c) else None
| _ => None
end.
Fixpoint find_shadow_decl (al : list (sv * sv)) (p : nat) (bx : sv) : option nat :=
match al with
| [] => None
| (l, r) :: al' =>
match l, r with
| SAlu ALU_ADD (SAlu ALU_SRL (SOff p' c0) (SLit k)) bx', SOff Sa z0 =>
if (Nat.eqb p' p) && (c0 =? 0) && (k =? 3) && (z0 =? 0) && sv_eqb bx' bx
then Some Sa else find_shadow_decl al' p bx
| _, _ => find_shadow_decl al' p bx
end
end.
Definition match_shadow_core (al : list (sv * sv)) (v : sv) : option (nat * Z * nat) :=
match v with
| SAlu ALU_ADD u w =>
match srl3_atom u with
| Some (p, c) =>
match find_shadow_decl al p w with Some Sa => Some (p, c, Sa) | None => None end
| None =>
match srl3_atom w with
| Some (p, c) =>
match find_shadow_decl al p u with Some Sa => Some (p, c, Sa) | None => None end
| None => None
end
end
| _ => None
end.
Definition shadow_norm_core (G : facts) (v : sv) (i : Z) : option (option nat * Z) :=
match match_shadow_core (f_alias G) v with
| Some (p, c, Sa) =>
match atom_lookup (f_atoms G) p, sv_range G (SOff p c) with
| Some f, Some _ => if 3 <=? af_al2 f then Some (Some Sa, c / 8 + i) else None
| _, _ => None
end
| None => None
end.
Definition shadow_norm (G : facts) (a : sv) : option (option nat * Z) :=
match shadow_norm_core G a 0 with
| Some r => Some r
| None =>
match a with
| SAlu ALU_ADD v (SLit i) => shadow_norm_core G v i
| _ => None
end
end.
Lemma zv_canon_add_l : forall x y, Z_to_bv 64 (zcanon x + y) = Z_to_bv 64 (x + y).
Proof.
intros x y. apply Z_to_bv64_eq_mod. unfold zcanon, M64.
rewrite Z.add_mod_idemp_l; [reflexivity | lia].
Qed.
Lemma zv_canon_add_r : forall x y, Z_to_bv 64 (x + zcanon y) = Z_to_bv 64 (x + y).
Proof.
intros x y. rewrite (Z.add_comm x (zcanon y)), zv_canon_add_l, Z.add_comm. reflexivity.
Qed.
Lemma srl3_atom_sound : forall v p c, srl3_atom v = Some (p, c) -> v = SAlu ALU_SRL (SOff p c) (SLit 3).
Proof.
intros v p c H. unfold srl3_atom in H. destruct v; try discriminate.
destruct op; try discriminate. destruct v1; try discriminate. destruct v2; try discriminate.
destruct (z0 =? 3) eqn:E; [|discriminate]. apply Z.eqb_eq in E. injection H as <- <-. subst. reflexivity.
Qed.
Lemma find_shadow_decl_sound : forall E al p bx Sa,
alias_ok E al -> find_shadow_decl al p bx = Some Sa ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) bx) = sv_denot E (SOff Sa 0).
Proof.
intros E al p bx Sa. induction al as [|[l r] al IH]; intros Hok H; [discriminate|].
cbn [find_shadow_decl] in H. destruct Hok as [Hlr Hal].
destruct l as [| | op u w | | | | | | | |]; try exact (IH Hal H).
destruct op; try exact (IH Hal H).
destruct u as [| | op2 u1 u2 | | | | | | | |]; try exact (IH Hal H).
destruct op2; try exact (IH Hal H).
destruct u1 as [|p' c0| | | | | | | | |]; try exact (IH Hal H).
destruct u2 as [k| | | | | | | | | |]; try exact (IH Hal H).
destruct r as [|Sa' z0| | | | | | | | |]; try exact (IH Hal H).
destruct ((p' =? p)%nat && (c0 =? 0) && (k =? 3) && (z0 =? 0) && sv_eqb w bx) eqn:Hc; [|exact (IH Hal H)].
injection H as <-.
apply andb_prop in Hc as [Hc Hbx]. apply andb_prop in Hc as [Hc Hz0]. apply andb_prop in Hc as [Hc Hk].
apply andb_prop in Hc as [Hp Hc0].
apply Nat.eqb_eq in Hp. apply Z.eqb_eq in Hc0. apply Z.eqb_eq in Hk. apply Z.eqb_eq in Hz0.
apply sv_eqb_eq in Hbx. subst. exact Hlr.
Qed.
Lemma U_srl3 : forall E x, U E (SAlu ALU_SRL x (SLit 3)) = U E x / 8.
Proof.
intros E x. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (U_range E x) as Hr. apply zcanon_id. unfold M64 in *.
split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
Qed.
Lemma match_shadow_core_denot : forall E G v p c Sa,
facts_ok E G -> match_shadow_core (f_alias G) v = Some (p, c, Sa) ->
Z_to_bv 64 (U E v) = Z_to_bv 64 (U E (SOff p c) / 8 - U E (SOff p 0) / 8 + bv_unsigned (ew E Sa)).
Proof.
intros E G v p c Sa HG H.
destruct HG as (_ & _ & Hal).
unfold match_shadow_core in H. destruct v as [| | op u w | | | | | | | |]; try discriminate.
destruct op; try discriminate.
assert (Hdecl : forall bx, find_shadow_decl (f_alias G) p bx = Some Sa ->
bv_unsigned (ew E Sa) = zcanon (U E (SOff p 0) / 8 + U E bx)).
{ intros bx Hf. pose proof (find_shadow_decl_sound E _ p bx Sa Hal Hf) as Hd.
apply (f_equal bv_unsigned) in Hd.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) bx) = U E (SOff Sa 0)) in Hd.
rewrite U_SOff, Z.add_0_r, (zcanon_id (bv_unsigned (ew E Sa))) in Hd by (pose proof (bv_unsigned_in_range 64 (ew E Sa)); unfold M64; change (bv_modulus 64) with (2^64) in *; lia).
rewrite <- Hd, U_SAlu. cbn [zalu_raw]. rewrite U_srl3. reflexivity. }
assert (Hgoal : forall bx, find_shadow_decl (f_alias G) p bx = Some Sa ->
Z_to_bv 64 (zcanon (U E (SOff p c) / 8 + U E bx))
= Z_to_bv 64 (U E (SOff p c) / 8 - U E (SOff p 0) / 8 + bv_unsigned (ew E Sa))).
{ intros bx Hf. rewrite (Hdecl bx Hf). rewrite Z_to_bv64_canon.
replace (U E (SOff p c) / 8 - U E (SOff p 0) / 8 + zcanon (U E (SOff p 0) / 8 + U E bx))
with ((U E (SOff p c) / 8 - U E (SOff p 0) / 8) + zcanon (U E (SOff p 0) / 8 + U E bx)) by lia.
rewrite zv_canon_add_r. apply Z_to_bv64_eq_mod. f_equal. lia. }
destruct (srl3_atom u) as [[p' c']|] eqn:Hu.
- destruct (find_shadow_decl (f_alias G) p' w) as [Sa'|] eqn:Hf; [|discriminate].
injection H as <- <- <-. apply srl3_atom_sound in Hu. subst u.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3. exact (Hgoal w Hf).
- destruct (srl3_atom w) as [[p' c']|] eqn:Hw; [|discriminate].
destruct (find_shadow_decl (f_alias G) p' u) as [Sa'|] eqn:Hf; [|discriminate].
injection H as <- <- <-. apply srl3_atom_sound in Hw. subst w.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3. rewrite (Z.add_comm (U E u)). exact (Hgoal u Hf).
Qed.
Lemma shadow_norm_core_sound : forall E G v i b off,
facts_ok E G -> shadow_norm_core G v i = Some (b, off) ->
Z_to_bv 64 (U E v + i) = Z_to_bv 64 (base_val E b + off).
Proof.
intros E G v i b off HG H. unfold shadow_norm_core in H.
destruct (match_shadow_core (f_alias G) v) as [[[p c] Sa]|] eqn:Hm; [|discriminate].
destruct (atom_lookup (f_atoms G) p) as [f|] eqn:Hf; [|discriminate].
destruct (sv_range G (SOff p c)) as [[lo hi]|] eqn:Hr; [|discriminate].
destruct (3 <=? af_al2 f) eqn:Hal; [|discriminate]. injection H as <- <-.
apply Z.leb_le in Hal.
pose proof (atom_lookup_ok E _ _ _ (proj1 HG) Hf) as (Hb & Hmod & Hk).
assert (Hnw : 0 <= bv_unsigned (ew E p) + c < M64).
{ cbn [sv_range] in Hr. rewrite Hf in Hr.
destruct (0 <=? af_lo f + c) eqn:H1; [|discriminate].
destruct (af_hi f + c <? M64) eqn:H2; [|discriminate].
apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
assert (H8 : bv_unsigned (ew E p) mod 8 = 0).
{ apply (Znumtheory.Zdivide_mod). apply (Z.divide_trans _ (2 ^ af_al2 f)).
- exists (2 ^ (af_al2 f - 3)). change 8 with (2 ^ 3). rewrite <- Z.pow_add_r by lia. f_equal. lia.
- apply Znumtheory.Zmod_divide; [apply Z.pow_nonzero; lia | exact Hmod]. }
pose proof (Z.div_mod (bv_unsigned (ew E p)) 8 ltac:(lia)) as Hdm. rewrite H8, Z.add_0_r in Hdm.
pose proof (bv_unsigned_in_range 64 (ew E p)) as Hpr. change (bv_modulus 64) with (2 ^ 64) in Hpr.
assert (Hpc : U E (SOff p c) = bv_unsigned (ew E p) + c) by (rewrite U_SOff; apply zcanon_id; exact Hnw).
assert (Hp0 : U E (SOff p 0) = bv_unsigned (ew E p)).
{ rewrite U_SOff, Z.add_0_r. apply zcanon_id. unfold M64. lia. }
assert (Hdiv : (bv_unsigned (ew E p) + c) / 8 = bv_unsigned (ew E p) / 8 + c / 8).
{ rewrite Hdm at 1. rewrite Z.mul_comm, Z.div_add_l by lia. reflexivity. }
cbn [base_val].
rewrite <- (zv_canon_add_l (U E v)).
change (zcanon (U E v)) with (bv_unsigned (Z_to_bv 64 (U E v)) ) || idtac.
pose proof (match_shadow_core_denot E G v p c Sa HG Hm) as Hcore.
rewrite Hpc, Hp0, Hdiv in Hcore.
replace (bv_unsigned (ew E p) / 8 + c / 8 - bv_unsigned (ew E p) / 8 + bv_unsigned (ew E Sa))
with (bv_unsigned (ew E Sa) + c / 8) in Hcore by lia.
rewrite (zv_canon_add_l (U E v)).
apply (f_equal bv_unsigned) in Hcore. rewrite !Z_to_bv_unsigned in Hcore.
apply Z_to_bv64_eq_mod. unfold bv_wrap in Hcore. change (bv_modulus 64) with (2 ^ 64) in Hcore.
rewrite <- Z.add_mod_idemp_l by lia. rewrite Hcore. rewrite Z.add_mod_idemp_l by lia. f_equal. lia.
Qed.
Theorem shadow_norm_sound : forall E G a b off,
facts_ok E G -> shadow_norm G a = Some (b, off) ->
sv_denot E a = Z_to_bv 64 (base_val E b + off).
Proof.
intros E G a b off HG H. unfold shadow_norm in H.
destruct (shadow_norm_core G a 0) as [r|] eqn:H0.
- injection H as ->. rewrite denot_lit_U, <- (Z.add_0_r (U E a)).
exact (shadow_norm_core_sound E G a 0 b off HG H0).
- destruct a as [| | op v w | | | | | | | |]; try discriminate.
destruct op; try discriminate. destruct w as [i| | | | | | | | | |]; try discriminate.
rewrite denot_lit_U, U_SAlu, U_SLit. cbn [zalu_raw]. rewrite Z_to_bv64_canon, zv_canon_add_r.
exact (shadow_norm_core_sound E G v i b off HG H).
Qed.
Lemma shadow_decl_ok : forall E (p b s : nat) (pv B : Z),
ew E p = Z_to_bv 64 pv -> 0 <= pv < 2 ^ 64 ->
ew E b = Z_to_bv 64 B ->
ew E s = Z_to_bv 64 (B + pv / 8) ->
sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff p 0) (SLit 3)) (SOff b 0)) = sv_denot E (SOff s 0).
Proof.
intros E p b s pv B Hp Hpv Hb Hs. apply U_inj.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_srl3, !U_SOff, Hp, Hb, Hs, !Z.add_0_r.
rewrite (unsigned_lit_small pv) by lia. rewrite (zcanon_id pv) by (unfold M64; lia).
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
unfold zcanon, M64. rewrite (Z.mod_mod B) by lia. rewrite Z.add_mod_idemp_r by lia.
rewrite (Z.mod_mod (B + pv / 8)) by lia. f_equal. lia.
Qed.
Lemma low32_add : forall a b : word, low32 (a + b)%bv = (low32 a + low32 b)%bv.
Proof.
intros a b. apply bv_eq. unfold low32. rewrite bv_add_unsigned, !extract_unsigned_mod, bv_add_unsigned.
unfold bv_wrap. change (bv_modulus 32) with (2 ^ 32). change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32). change (2 ^ Z.of_N 32) with (2 ^ 32).
rewrite Zaux.Zmod_mod_mult by lia. rewrite <- Zplus_mod. reflexivity.
Qed.
Lemma low32_sext32 : forall x : bv 32, low32 (sext 64 x) = x.
Proof.
intros x. rewrite sext64_lit, low32_lit. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold bv_signed, bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
pose proof (bv_unsigned_in_range 32 x) as Hx. change (bv_modulus 32) with 4294967296 in Hx.
set (u := bv_unsigned x) in *.
pose proof (Z.div_mod (u + 2147483648) 4294967296 ltac:(lia)) as Hdm.
pose proof (Z.mod_pos_bound (u + 2147483648) 4294967296 ltac:(lia)) as Hmb.
set (q := (u + 2147483648) / 4294967296) in *.
replace ((u + 2147483648) mod 4294967296 - 2147483648) with (u + (- q) * 4294967296) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Section d.
Variable segs : list Segment.
Variable tbl : ctable.
Context {fx : FPState}.
Definition sym_step_sh (ss : sstate) : sres :=
match sym_step segs tbl ss with
| SStop why =>
let G := ss_facts ss in
let R := sr_get (ss_regs ss) in
match clookup tbl (ss_pc ss) with
| None => SStop why
| Some wz =>
let w := Z_to_bv 32 wz in
if is_ecall w then SStop why else
match decode_any w with
| Some (Load sz sg rd rs1 imm, isz) =>
if negb (isz =? 4) then SStop why else
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match shadow_norm G a with
| Some (b, off) =>
match sload segs G (ss_mem ss) b off sz sg with
| Some v => SRun (setreg ss rd v (ss_pc ss + 4))
| None => SStop (SR_load b off)
end
| None => SStop why
end
| Some (Store sz rs1 rs2 imm, isz) =>
if negb (isz =? 4) then SStop why else
match ss_resv ss with
| Some _ => SStop SR_resv
| None =>
let a := s_alu2 G ALU_ADD (R rs1) (SLit (bv_signed imm)) in
match shadow_norm G a with
| Some (b, off) =>
match sstore (ss_mem ss) b off sz (R rs2) with
| Some m' => SRun (mkSST (ss_pc ss + 4) (ss_regs ss) (ss_fregs ss) m' None G)
| None => SStop (SR_store b off)
end
| None => SStop why
end
end
| Some (Amo AMO_ADD wd _ _ rd rs1 rs2, isz) =>
if negb (isz =? 4) then SStop why else
match ss_resv ss with
| Some _ => SStop SR_resv
| None =>
let a := R rs1 in
if negb (aligned_dec G a (amo_bytes_of wd)) then SStop SR_align else
match addr_of a with
| None => SStop (SR_addr a)
| Some (b, off) =>
match sload segs G (ss_mem ss) b off (amo_sz wd) true with
| None => SStop (SR_load b off)
| Some v =>
match sstore (ss_mem ss) b off (amo_sz wd) (s_alu2 G ALU_ADD v (R rs2)) with
| Some m' => SRun (mkSST (ss_pc ss + 4) (sr_set (ss_regs ss) rd v) (ss_fregs ss) m' None G)
| None => SStop (SR_store b off)
end
end
end
end
| _ => SStop why
end
end
| r => r
end.
Fixpoint sym_run_sh (fuel : nat) (ss : sstate) : sstate * run_status :=
match fuel with
| O => (ss, RS_running)
| S f => match sym_step_sh ss with
| SRun ss' => sym_run_sh f ss'
| SEcall ss' => (ss', RS_ecall)
| SStop why => (ss, RS_stopped why)
end
end.
Fixpoint sym_run_to_sh (fuel : nat) (stop_pc : Z) (ss : sstate) : sstate * run_status :=
match fuel with
| O => (ss, RS_running)
| S f => if ss_pc ss =? stop_pc then (ss, RS_running) else
match sym_step_sh ss with
| SRun ss' => sym_run_to_sh f stop_pc ss'
| SEcall ss' => (ss', RS_ecall)
| SStop why => (ss, RS_stopped why)
end
end.
Definition sym_runN_sh (n : N) (ss : sstate) := sym_run_sh (N.to_nat n) ss.
Definition sym_run_toN_sh (n : N) (stop : Z) (ss : sstate) := sym_run_to_sh (N.to_nat n) stop ss.
Hypothesis Htbl : table_ok segs tbl.
Section e.
Variable P1 : env -> list sv -> bvmap 5 word -> Prop.
Variable P5 : list sv -> bv 32 -> Prop.
Local Notation st_okP := (st_okP segs P1 P5).
Local Notation st_okP_ecall := (st_okP_ecall segs P1 P5).
Theorem sym_step_sh_soundP : forall E ss ss' ms,
st_okP E ss ms -> sym_step_sh ss = SRun ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okP E ss' ms'
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros E ss ss' ms HS H. unfold sym_step_sh in H.
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
{ injection H as <-. exact (sym_step_soundP segs tbl Htbl P1 P5 E ss ss1 ms HS Hs). }
{ discriminate. }
clear Hs.
destruct ms as [regs fregs pcv pend resv fcsr mem rom].
destruct HS as (Hfr & Hpc & Hpend & Hresv & Hfcsr & Hrom & Hregs & Hmem & HG); cbn in *.
subst pcv pend rom.
destruct (clookup tbl (ss_pc ss)) as [wz|] eqn:Hlk; [|discriminate].
pose proof (Htbl (ss_pc ss) wz Hlk) as Hf. cbv zeta in H.
rewrite (step_on_fetch segs _ (Z_to_bv 32 wz)) by exact Hf.
rewrite (decode_exec_compat segs). destruct (is_ecall (Z_to_bv 32 wz)) eqn:Hec; [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|] eqn:Hd; [|discriminate].
assert (HR : forall r, rget (Core regs fregs (Z_to_bv 64 (ss_pc ss)) fcsr resv) r
= sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. rewrite rget_regs. apply Hregs. }
destruct i; try discriminate; try match goal with op : amoop |- _ => destruct op; try discriminate end;
destruct (isz =? 4) eqn:Hsz; cbn [negb] in H; try discriminate; apply Z.eqb_eq in Hsz; subst isz;
cbv beta iota zeta delta
[interp_eff0 RiscvSemantics.width_bytes RiscvSemantics.width_bytesZ
Sem.exec Sem.load_val Sem.store_val
Sem.with_regs Sem.with_pc Sem.with_resv
Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv
ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom ms_fregs ms_fcsr];
rewrite ?rset_core; cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?HR.
-
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (shadow_norm (ss_facts ss) a) as [[b off]|] eqn:Hao; [|discriminate].
destruct (sload segs (ss_facts ss) (ss_mem ss) b off sz signed) as [v|] eqn:Hsl; [|discriminate].
injection H as <-.
pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
{ rewrite <- (shadow_norm_sound E (ss_facts ss) a b off HG Hao). subst a.
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
rewrite Haddr.
destruct sz; cbn [nbytes nbits] in Hrd, Hv;
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite ov_rdn, Hrd; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
eexists; (split; [reflexivity|]); (split; [|cbn [ms_mem]; apply frame_of_refl]);
(apply (st_ok_mach segs P1 P5); cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4]);
rewrite Hv, ?bv_extract_0_64; cbn [load_result nbits]; destruct signed; reflexivity.
-
destruct (ss_resv ss) as [rv0|] eqn:Hrv; [discriminate|]. cbn in Hresv. subst resv.
remember (s_alu2 (ss_facts ss) ALU_ADD (sr_get (ss_regs ss) rs1) (SLit (bv_signed imm))) as a eqn:Ha.
destruct (shadow_norm (ss_facts ss) a) as [[b off]|] eqn:Hao; [|discriminate].
destruct (sstore (ss_mem ss) b off sz (sr_get (ss_regs ss) rs2)) as [m'|] eqn:Hst; [|discriminate].
injection H as <-.
pose proof (sstore_sound segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
assert (Haddr : (sv_denot E (sr_get (ss_regs ss) rs1) + sext 64 imm)%bv = Z_to_bv 64 (base_val E b + off)).
{ rewrite <- (shadow_norm_sound E (ss_facts ss) a b off HG Hao). subst a.
rewrite s_alu2_sound by exact HG. cbn [sv_denot]. rewrite sext64_lit. reflexivity. }
rewrite Haddr.
destruct sz; cbn [nbytes nbits] in Hok, Hmem';
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite Hok; unfold inval_resv;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv];
rewrite ?st_bytes_8, ?st_bytes_16, ?st_bytes_32, ?st_bytes_64, write_to_mem_wbytes;
eexists; (split; [reflexivity|]);
(split; [apply (st_ok_mach segs P1 P5); cbn; auto; apply pc_plus4
| cbn [ms_mem]; eapply store_region_frame; [exact Hmem| | cbn; lia] ]).
all: unfold sstore in Hst; unfold st_bytes; rewrite length_zbytes; exact Hst.
-
destruct (ss_resv ss) as [rv0|] eqn:Hrv; [discriminate|]. cbn in Hresv. subst resv.
destruct (aligned_dec (ss_facts ss) (sr_get (ss_regs ss) rs1) (amo_bytes_of w)) eqn:Hal;
cbn [negb] in H; [|discriminate].
destruct (addr_of (sr_get (ss_regs ss) rs1)) as [[b off]|] eqn:Hao; [|discriminate].
destruct (sload segs (ss_facts ss) (ss_mem ss) b off (amo_sz w) true) as [v|] eqn:Hsl; [|discriminate].
destruct (sstore (ss_mem ss) b off (amo_sz w) (s_alu2 (ss_facts ss) ALU_ADD v (sr_get (ss_regs ss) rs2))) as [m'|] eqn:Hst; [|discriminate].
injection H as <-.
pose proof (sload_sound segs E _ mem _ _ _ _ _ v HG Hmem Hsl) as (bs & Hrd & Hv).
pose proof (sstore_sound segs E mem _ _ _ _ _ m' Hmem Hst) as [Hok Hmem'].
pose proof (addr_of_sound E (ss_facts ss) _ b off HG Hao) as Haddr.
assert (Hamo : amo_aligned w (sv_denot E (sr_get (ss_regs ss) rs1)) = true).
{ unfold amo_aligned. apply Z.eqb_eq.
apply (aligned_dec_sound P1 E (ss_facts ss)); [exact HG| destruct w; cbn; lia |].
destruct w; exact Hal. }
rewrite Hamo. cbn [negb]. unfold inval_resv. cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
rewrite Haddr in *.
destruct w; cbn [amo_sz nbytes nbits] in Hrd, Hv, Hok, Hmem';
cbv beta iota zeta delta [interp_eff0 RiscvSemantics.width_bytes];
rewrite ov_rdn, Hrd, Hok; rewrite ?rset_core;
cbv beta iota zeta delta [Sem.c_regs Sem.c_fregs Sem.c_pc Sem.c_fcsr Sem.c_resv].
+
replace (amo_val AMO_ADD (bv_extract 0 32 (le_bytes_to_word bs)) (low32 (sv_denot E (sr_get (ss_regs ss) rs2))))
with (low32 (sv_denot E (s_alu2 (ss_facts ss) ALU_ADD v (sr_get (ss_regs ss) rs2)))).
2:{ rewrite s_alu2_sound by exact HG. cbn [alu64 sv_denot]. rewrite Hv. cbn [load_result nbits].
unfold amo_val, alu64, alu. rewrite low32_add, low32_sext32. reflexivity. }
rewrite st_bytes_32, write_to_mem_wbytes.
eexists; (split; [reflexivity|]).
split; [apply (st_ok_mach segs P1 P5); cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4]
| cbn [ms_mem]; eapply store_region_frame; [exact Hmem| | cbn; lia] ].
* rewrite Hv. cbn [load_result nbits]. reflexivity.
* unfold sstore in Hst; unfold st_bytes; rewrite length_zbytes; exact Hst.
+
replace (amo_val AMO_ADD (bv_extract 0 64 (le_bytes_to_word bs)) (sv_denot E (sr_get (ss_regs ss) rs2)))
with (sv_denot E (s_alu2 (ss_facts ss) ALU_ADD v (sr_get (ss_regs ss) rs2))).
2:{ rewrite s_alu2_sound by exact HG. cbn [alu64 sv_denot]. rewrite Hv, ?bv_extract_0_64. cbn [load_result nbits].
unfold amo_val, alu64, alu. rewrite ?bv_extract_0_64. reflexivity. }
rewrite st_bytes_64, write_to_mem_wbytes.
eexists; (split; [reflexivity|]).
split; [apply (st_ok_mach segs P1 P5); cbn; auto; [apply regs_ok_set'; [exact Hregs|] | apply pc_plus4]
| cbn [ms_mem]; eapply store_region_frame; [exact Hmem| | cbn; lia] ].
* rewrite Hv, ?bv_extract_0_64. cbn [load_result nbits]. reflexivity.
* unfold sstore in Hst; unfold st_bytes; rewrite length_zbytes; exact Hst.
Qed.
Theorem sym_step_sh_ecallP : forall E ss ss' ms,
st_okP E ss ms -> sym_step_sh ss = SEcall ss' ->
exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ st_okP_ecall E ss' ms'
/\ ms_mem ms' = ms_mem ms /\ ss' = ss.
Proof.
intros E ss ss' ms HS H. unfold sym_step_sh in H.
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
- discriminate.
- injection H as <-. exact (sym_step_ecallP segs tbl Htbl P1 P5 E ss ss1 ms HS Hs).
- exfalso. destruct (clookup tbl (ss_pc ss)) as [wz|]; [|discriminate]. cbv zeta in H.
destruct (is_ecall (Z_to_bv 32 wz)); [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|]; [|discriminate].
destruct i; try discriminate; try match goal with op : amoop |- _ => destruct op; try discriminate end;
destruct (isz =? 4); cbn [negb] in H; try discriminate.
+ destruct (shadow_norm _ _) as [[b off]|]; [|discriminate]. destruct (sload _ _ _ _ _ _ _); discriminate.
+ destruct (ss_resv ss); [discriminate|]. destruct (shadow_norm _ _) as [[b off]|]; [|discriminate].
destruct (sstore _ _ _ _ _); discriminate.
+ destruct (ss_resv ss); [discriminate|]. destruct (aligned_dec _ _ _); cbn [negb] in H; [|discriminate].
destruct (addr_of _) as [[b off]|]; [|discriminate]. destruct (sload _ _ _ _ _ _ _); [|discriminate].
destruct (sstore _ _ _ _ _); discriminate.
Qed.
Lemma sym_step_sh_skeleton : forall ss ss',
sym_step_sh ss = SRun ss' -> skeleton (ss_mem ss') = skeleton (ss_mem ss).
Proof.
intros ss ss' H. unfold sym_step_sh in H.
destruct (sym_step segs tbl ss) as [ss1|ss1|why] eqn:Hs.
{ injection H as <-. exact (sym_step_skeleton segs tbl ss ss1 Hs). }
{ discriminate. }
destruct (clookup tbl (ss_pc ss)) as [wz|]; [|discriminate]. cbv zeta in H.
destruct (is_ecall (Z_to_bv 32 wz)); [discriminate|].
destruct (decode_any (Z_to_bv 32 wz)) as [[i isz]|]; [|discriminate].
destruct i; try discriminate; try match goal with op : amoop |- _ => destruct op; try discriminate end;
destruct (isz =? 4); cbn [negb] in H; try discriminate.
- destruct (shadow_norm _ _) as [[b off]|]; [|discriminate].
destruct (sload _ _ _ _ _ _ _); [|discriminate]. injection H as <-. reflexivity.
- destruct (ss_resv ss); [discriminate|]. destruct (shadow_norm _ _) as [[b off]|]; [|discriminate].
destruct (sstore _ _ _ _ _) eqn:Hst; [|discriminate]. injection H as <-. cbn.
eapply store_region_skeleton. exact Hst.
- destruct (ss_resv ss); [discriminate|]. destruct (aligned_dec _ _ _); cbn [negb] in H; [|discriminate].
destruct (addr_of _) as [[b off]|]; [|discriminate]. destruct (sload _ _ _ _ _ _ _); [|discriminate].
destruct (sstore _ _ _ _ _) eqn:Hst; [|discriminate]. injection H as <-. cbn.
eapply store_region_skeleton. exact Hst.
Qed.
Theorem sym_run_sh_soundP : forall fuel E ss ss' st ms,
st_okP E ss ms -> sym_run_sh fuel ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okP_ecall E ss' ms'
| _ => st_okP E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros E ss ss' st ms HS H; cbn [sym_run_sh] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
- destruct (sym_step_sh ss) as [ss1|ss1|why] eqn:Hs.
+ destruct (sym_step_sh_soundP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_step_sh_skeleton ss ss1 Hs) as Hsk1.
destruct (IH E ss1 ss' st ms1 HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+ injection H as <- <-.
destruct (sym_step_sh_ecallP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss). subst ss1.
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
Qed.
Theorem sym_run_to_sh_soundP : forall fuel stop E ss ss' st ms,
st_okP E ss ms -> sym_run_to_sh fuel stop ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with
| RS_ecall => st_okP_ecall E ss' ms'
| _ => st_okP E ss' ms'
end /\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
induction fuel as [|fuel IH]; intros stop E ss ss' st ms HS H; cbn [sym_run_to_sh] in H.
- injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
- destruct (ss_pc ss =? stop).
{ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl]. }
destruct (sym_step_sh ss) as [ss1|ss1|why] eqn:Hs.
+ destruct (sym_step_sh_soundP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hfr1).
pose proof (sym_step_sh_skeleton ss ss1 Hs) as Hsk1.
destruct (IH stop E ss1 ss' st ms1 HS1 H) as (ms' & Hms & HS' & Hsk & Hfr).
exists ms'. split.
{ eapply mst_step; [| exact Hstep | exact Hms]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS'|]. split; [congruence|].
eapply frame_of_trans; [symmetry; exact Hsk1 | exact Hfr1 | exact Hfr].
+ injection H as <- <-.
destruct (sym_step_sh_ecallP E ss ss1 ms HS Hs) as (ms1 & Hstep & HS1 & Hm & Hss). subst ss1.
exists ms1. split.
{ eapply mst_step; [| exact Hstep | apply mst_refl]. destruct HS as (_ & _ & Hp & _). exact Hp. }
split; [exact HS1|]. split; [reflexivity|]. rewrite Hm. apply frame_of_refl.
+ injection H as <- <-. exists ms. split; [apply mst_refl|]. split; [exact HS|]. split; [reflexivity| apply frame_of_refl].
Qed.
End e.
Theorem sym_run_sh_sound : forall n E ss ss' st ms,
st_ok segs E ss ms -> sym_runN_sh n ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
/\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. intros n. exact (sym_run_sh_soundP P1_pin P5_pin (N.to_nat n)). Qed.
Theorem sym_run_to_sh_sound : forall n stop E ss ss' st ms,
st_ok segs E ss ms -> sym_run_toN_sh n stop ss = (ss', st) ->
exists ms', msteps segs ms ms' /\
match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
/\ skeleton (ss_mem ss') = skeleton (ss_mem ss) /\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof. intros n stop. exact (sym_run_to_sh_soundP P1_pin P5_pin (N.to_nat n) stop). Qed.
Lemma msteps_run_sh : forall n E ss ss' st ms,
st_ok segs E ss ms -> sym_runN_sh n ss = (ss', st) ->
exists ms', msteps segs ms ms'
/\ match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n E ss ss' st ms HS Hrun.
destruct (sym_run_sh_sound n E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr). exists ms'. auto.
Qed.
Lemma msteps_run_to_sh : forall n stop E ss ss' st ms,
st_ok segs E ss ms -> sym_run_toN_sh n stop ss = (ss', st) ->
exists ms', msteps segs ms ms'
/\ match st with RS_ecall => st_ok_ecall segs E ss' ms' | _ => st_ok segs E ss' ms' end
/\ frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms').
Proof.
intros n stop E ss ss' st ms HS Hrun.
destruct (sym_run_to_sh_sound n stop E ss ss' st ms HS Hrun) as (ms' & Hms & HS' & _ & Hfr). exists ms'. auto.
Qed.
End d.
Ltac sym_why_sh segs tbl ss :=
let r := eval vm_compute in (sym_step_sh segs tbl ss) in
lazymatch r with
| SStop ?why => why
| _ => fail "sym_why_sh: state is not stuck"
end.
