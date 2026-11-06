(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AC8j.v at c8557374ad2e (st_ok_region_nth, field_of_region, as pa_i_region_nth over a restricted state and pa_i_field) and proofs/reac-pw/fuzz_role/lib/Reusable/YCbq.v at a0d3fb0309b (aj_intrin_at, as pa_i_memset_at: at OSet on rsegs, its post adds same_io from the contract's same_but_materialized); the rest of the file is new: the block lemma pa_int7 of LLVMFuzzerTestOneInput's shape-7 Int pod block and its helpers. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropIntB.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address relocated (role image A -> headamp image A); pp in its own env slot (atom 35, the value of the cell R+0xf0: s11 holds the input cursor here), so the entry and resume states, the shadow entry, the alias fact and the len region name atom 35 for role's 27; the cells move by the slot map (R+0xb8 -> R+0xd8, R+0xe0 -> R+0x100, R+0xe8 -> R+0x108) and the index register is a7 (role a6); pa_i_memset_at removed, the call is lib/A/HPgIntrin.v hd_memset_at; kept_run / same_io_wvb from lib/A/HPgPropKit.v / HPgSteps.v; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgPropIntB.v, with its module paths and module names changed; 362 of its 424 lines of code are new or changed and 390 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgPropKeyB.v at a529a88a618 for reac-pw/fuzz_headamp image A: every address read off headamp's listing; pp has its own env slot 36, read from the cell R+0xf0 before each put (s11 holds the input cursor), with the alias, the s4 / s5 values, the shadow entry and the write window over that slot; the cells move by the plan's slot map (R+0x38 -> R+0x50, R+0x48 -> R+0x70, R+0x88 -> R+0xa8, R+0xa0 -> R+0xc0, R+0xd0 -> R+0xe8, R+0xe0 -> R+0x100, R+0xe8 -> R+0x108); the frame is 0x1e0 bytes; module paths. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on its unstripped
   twin sha256 b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a): the key block SELK 0x81514 of the
   property loop of LLVMFuzzerTestOneInput (0x80bc0), as a block lemma over lib/A/HPgPropKit.v. Proves no function
   (kind: segment lemma).

   THE BLOCK 0x81514 -> 0x8165c (params Struct) / 0x82808 (Int 7), pod.h:177-180 twice (pod_put32) and 405-412:
     0x81514 andi a3,a1,3; ld a4,0x100(s1); 0x8151c bltu a2,a4 (the capacity test, not taken: a2 = len - 0x3ffd);
     0x81520 ld a4,0x70(s1) (0x80001); 0x81524 bnez a3; 0x81528 ld a4,0x50(s1) (0x10003, when a3 = 0);
     0x8152c ld a2,0xf0(s1) (pp); 0x81530 add a0,a2,a0 (pp + len); the shadow checks of a0 0x8153c and a0 + 3 0x81554
     (EQ-J, out-of-line slow blocks 0x82b48 / 0x82b58 never reached: the shadow bytes of pp's block are 0); the four
     byte stores of a4; the check of pp->len 0x81578; len += 4; 0x81590 the second capacity test (not taken);
     0x815b0 ld a2,0xf0(s1) (pp); the checks of pp + len + 4 (0x815c0 / 0x815d8, slow blocks 0x82b68 / 0x82b78 never
     reached); four zero bytes; len += 4;
     0x8160c a0 = s9, 0x81610 beqz a3 (a0 = 1 when a3 <> 0), seen' -> R+0xa8; first := snez(a3) & seqz(s9) -> R+0xe8;
     a1 := snez(a3) & seqz(sel & 0x10); at := len -> R+0xc0; a0 := at + R+0x108; 0x81654 bnez a1.
   THE ROUTE. One straight run of the token engine per case of (sel mod 4 = 0, bit 4 of sel, seen): the entry
   facts carry the case as alias facts (sel & 3 -> 0 or the atom 34 = sel mod 4 in [1, 3]; sel & 0x10 -> 0 or 0x10)
   and seen as an exact atom fact, so every data branch and every value is decided. pp is the atom 36, the value of
   the cell R+0xf0 (s11 holds the input cursor and is not read); pp + len is the atom 33 (alias of pp + a0), with its
   own write window [0, 8) and shadow entry [0, 16) (the four checks then read 0); the two capacity tests are decided
   by the ranges of atom 12 (a2 = len - 0x3ffd) and of the atom 35 (alias of len + 4 - 0x3ffd). The write rights:
   pp's block was made since the journal's start (hd_fresh_awr), the slots R+0xa8 / R+0xc0 / R+0xe8 lie in the
   caller's stack window. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgSteps HPgMem HPgPropKit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the entry state of 0x81514 ----
   env slots: 0 .. 31 the registers (9 R, 10 len, 11 sel, 12 len - 0x3ffd, 25 seen), 32 the shadow offset K,
   33 pp + len, 34 sel mod 4, 35 len + 4 - 0x3ffd, 36 pp (the cell R+0xf0). *)
Definition pa_k_x (pp plen sel : Z) : list Z := [pp + plen; sel mod 4; plen - 16377; pp].
(* the shadow entries: pp's whole block, and the 16 bytes from pp + len *)
Definition pa_k_SH : list shent := [mkSHE 36 0 19744; mkSHE 33 0 16].
Definition pa_k_atoms (s : Z) : list (nat * afact) :=
[ (9%nat, mkAF 70368744177664 140737488355328 4); (36%nat, mkAF 4096 140737479946976 4);
  (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 0 5424 0); (11%nat, mkAF 0 255 0); (25%nat, mkAF s s 0);
  (33%nat, mkAF 4096 140737479952400 0); (12%nat, mkAF 18446744073709535235 18446744073709540659 0);
  (35%nat, mkAF 18446744073709535239 18446744073709540663 0) ].
(* the case: z3 = (sel mod 4 =? 0), b4 = bit 4 of sel *)
Definition pa_k_ex (z3 : bool) : list (nat * afact) := if z3 then [] else [(34%nat, mkAF 1 3 0)].
Definition pa_k_al (z3 b4 : bool) : list (sv * sv) :=
[ (SAlu ALU_AND (SOff 11 0) (SLit 3), if z3 then SLit 0 else SOff 34 0);
  (SAlu ALU_AND (SOff 11 0) (SLit 16), SLit (if b4 then 16 else 0)) ].
Definition pa_k_al0 : list (sv * sv) :=
[ (SAlu ALU_ADD (SOff 36 0) (SOff 10 0), SOff 33 0); (SOff 10 (-16377), SOff 35 0) ].
Definition pa_k_facts (z3 b4 : bool) (s : Z) : facts :=
mkFacts (pa_k_atoms s ++ pa_k_ex z3) [] (pa_k_al0 ++ pa_k_al z3 b4).
(* s4 = shadow address of pp + 0x4000, s5 = pp + 0x4000, s7 = K *)
Definition pa_k_regs : list sv :=
sr_set (sr_set (sr_set sr_atoms (20%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 16384) (SLit 3)) (SOff 32 0)))
  (21%bv : bv 5) (SOff 36 16384)) (23%bv : bv 5) (SOff 32 0).
Definition pa_k_mem : smem :=
[ YP09.mkRegion (Some 9%nat) 0x50 0x78 0 0
    [ YP09.mkChunk 0x50 (CVal 8 (SLit 0x10003)); YP09.mkChunk 0x70 (CVal 8 (SLit 0x80001)) ];
  YP09.mkRegion (Some 9%nat) 0xa8 0xb0 0xa8 0xb0 [];
  YP09.mkRegion (Some 9%nat) 0xc0 0xc8 0xc0 0xc8 [];
  YP09.mkRegion (Some 9%nat) 0xe8 0xf0 0xe8 0xf0 [];
  YP09.mkRegion (Some 9%nat) 0xf0 0x110 0 0
    [ YP09.mkChunk 0xf0 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x100 (CVal 8 (SLit (-16385)));
      YP09.mkChunk 0x108 (CVal 8 (SLit (-16381))) ];
  YP09.mkRegion (Some 36%nat) 0x4000 0x4008 0x4000 0x4008 [ YP09.mkChunk 0x4000 (CVal 8 (SOff 10 0)) ];
  YP09.mkRegion (Some 33%nat) 0 8 0 8 [] ].
Definition ss_key (z3 b4 : bool) (s : Z) : sstate := mkSS PA_SELK pa_k_regs pa_k_mem None (pa_k_facts z3 b4 s).

(* ---- small arithmetic ---- *)
Lemma pa_k_land3 : forall a, Z.land a 3 = a mod 4.
Proof. intros a. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma pa_k_land16 : forall a, Z.land a 16 = if Z.testbit a 4 then 16 else 0.
Proof.
intros a. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec.
change 16 with (2 ^ 4). rewrite Z.pow2_bits_eqb by lia.
destruct (Z.testbit a 4) eqn:Hb.
- rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 4 i) as [<-|Hne]; [rewrite Hb; reflexivity | apply andb_false_r].
- rewrite Z.bits_0. destruct (Z.eqb_spec 4 i) as [<-|Hne]; [rewrite Hb; reflexivity | apply andb_false_r].
Qed.

Section h. Context {fx : YK11.FPState}.
Lemma pa_k_soff : forall E n c v, bv_unsigned (ew E n) = v -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n c v Hn. cbn [sv_denot]. rewrite Hn. reflexivity. Qed.
Lemma pa_k_and_lit : forall E n x k, bv_unsigned (ew E n) = x -> 0 <= x < 2 ^ 64 -> 0 <= k < 2 ^ 63 ->
sv_denot E (SAlu ALU_AND (SOff n 0) (SLit k)) = Z_to_bv 64 (Z.land x k).
Proof.
intros E n x k Hn Hx Hk. cbn [sv_denot]. rewrite Hn, Z.add_0_r, and_lit_Z. f_equal.
unfold YP0m.zsigned64, zcanon, M64. rewrite !Z.mod_small by lia.
destruct (Z.ltb_spec k (2 ^ 63)); [reflexivity | lia].
Qed.
(* an override of a register by an expression of its value keeps regs_ok *)
Lemma pa_k_override : forall E sr regs (r : bv 5) e,
regs_ok E sr regs -> bv_eqb r 0 = false -> sv_denot E e = getr regs r -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e Hr Hr0 Hv rr. destruct (base.decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. symmetry. exact Hv.
- rewrite sr_get_set_other by exact Hne. apply Hr.
Qed.
(* every register outside clob still holds its entry value: its symbolic value is the entry state's *)
Lemma pa_k_regs_kept : forall E ss ms sr0 regs0 (H : word -> bool) (clob : list (bv 5)),
st_ok rsegs E ss (restrict H ms) -> regs_ok E sr0 regs0 ->
forallb (fun r : bv 5 => existsb (fun c => bv_eqb c r) clob || sv_eqb (sr_get (ss_regs ss) r) (sr_get sr0 r)) nz_regs = true ->
forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr (ms_regs ms) r = getr regs0 r.
Proof.
intros E ss ms sr0 regs0 H clob HS HR Hck r Hr0 Hn.
pose proof (proj1 (forallb_forall _ _) Hck r (in_nz_regs r Hr0)) as Hq. cbn beta in Hq.
apply orb_prop in Hq as [Hq|Hq].
- exfalso. apply existsb_exists in Hq as (c & Hc & Hb). apply bv_eqb_eq in Hb. subst c. exact (Hn Hc).
- apply sv_eqb_eq in Hq. rewrite (st_ok_restrict_reg rsegs H E ss ms r HS), Hq. symmetry. apply HR.
Qed.
Lemma pa_k_atoms_app : forall E l1 l2, atoms_ok E l1 -> atoms_ok E l2 -> atoms_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[n f] l IH]; cbn in *; [exact H2 | tauto]. Qed.
Lemma pa_k_alias_app : forall E l1 l2, alias_ok E l1 -> alias_ok E l2 -> alias_ok E (l1 ++ l2).
Proof. intros E l1 l2 H1 H2. induction l1 as [|[a b] l IH]; cbn in *; [exact H2 | tauto]. Qed.

(* ---- reading the end state: an 8-byte chunk, and the byte chunks of a region ---- *)
Definition pa_k_find (n : nat) (rs : smem) (o : Z) : option sv :=
match List.find (fun r => match YP09.r_base r with Some m => Nat.eqb m n | None => false end &&
  existsb (fun c => (YP09.c_off c =? o) && match YP09.c_val c with CVal w _ => N.eqb w 8 | _ => false end) (YP09.r_chunks r)) rs with
| Some r =>
  match List.find (fun c => (YP09.c_off c =? o) && match YP09.c_val c with CVal w _ => N.eqb w 8 | _ => false end) (YP09.r_chunks r) with
  | Some c => match YP09.c_val c with CVal _ v => Some v | _ => None end
  | None => None
  end
| None => None
end.
Lemma pa_k_slot : forall E ss ms (H : word -> bool) n b o e v,
st_ok rsegs E ss (restrict H ms) -> pa_k_find n (ss_mem ss) o = Some e -> bv_unsigned (ew E n) = b ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> val_mem rsegs (mrestrict H (ms_mem ms)) (b + o) 8 v.
Proof.
intros E ss ms H n b o e v HS Hf Hn He Hv. unfold pa_k_find in Hf.
destruct (List.find _ (ss_mem ss)) as [r|] eqn:Hr; [|discriminate].
apply find_some in Hr as [Hr Hq]. apply andb_prop in Hq as [Hbase _].
destruct (YP09.r_base r) as [m|] eqn:Hrb; [|discriminate]. apply Nat.eqb_eq in Hbase. subst m.
destruct (List.find _ (YP09.r_chunks r)) as [c|] eqn:Hc; [|discriminate].
apply find_some in Hc as [Hc Hq]. apply andb_prop in Hq as [Ho Hw]. apply Z.eqb_eq in Ho.
destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in *. subst co.
destruct cv as [w e'| | | ]; try discriminate. apply N.eqb_eq in Hw. subst w. injection Hf as Hf. subst e'.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hrb in Hck. cbn [base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E _ b o 8 e v Hck He ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Definition pa_k_bytes_b (n : nat) (rs : smem) (l : list Z) : bool :=
forallb (fun j => (0 <=? nth j l 0) && (nth j l 0 <? 256) &&
  existsb (fun r => match YP09.r_base r with Some m => Nat.eqb m n | None => false end &&
    existsb (fun c => (YP09.c_off c =? Z.of_nat j) &&
      match YP09.c_val c with CVal w (SLit z) => N.eqb w 1 && (z mod 256 =? nth j l 0) | _ => false end)
    (YP09.r_chunks r)) rs) (seq 0 (length l)).
Lemma pa_k_bytes : forall E ss ms (H : word -> bool) n b l,
st_ok rsegs E ss (restrict H ms) -> pa_k_bytes_b n (ss_mem ss) l = true -> bv_unsigned (ew E n) = b ->
garr8 rsegs (mrestrict H (ms_mem ms)) b l.
Proof.
intros E ss ms H n b l HS Hb Hn j Hj.
assert (Hjs : In j (seq 0 (length l))) by (apply in_seq; lia).
pose proof (proj1 (forallb_forall _ _) Hb j Hjs) as Hq. cbn beta in Hq.
apply andb_prop in Hq as [Hq Hex]. apply andb_prop in Hq as [H0 H256]. apply Z.leb_le in H0. apply Z.ltb_lt in H256.
split; [|lia].
apply existsb_exists in Hex as (r & Hr & Hq). apply andb_prop in Hq as [Hbase Hc].
destruct (YP09.r_base r) as [m|] eqn:Hrb; [|discriminate]. apply Nat.eqb_eq in Hbase. subst m.
apply existsb_exists in Hc as (c & Hc & Hq). apply andb_prop in Hq as [Ho Hw].
apply Z.eqb_eq in Ho. destruct c as [co cv]. cbn [YP09.c_off YP09.c_val] in *. subst co.
destruct cv as [w [z| | | | | | | | | | ]| | | ]; try discriminate.
apply andb_prop in Hw as [Hw Hz]. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hz. subst w.
destruct (st_ok_mem_ok rsegs E ss (restrict H ms) HS) as (_ & Hrs & _).
pose proof (proj1 (Forall_forall _ _) Hrs r Hr) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. rewrite Hrb in Hck. cbn [base_val] in Hck. rewrite Hn in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bt & Hcb & Hmb). cbn [cbyte YP09.c_val] in Hcb. injection Hcb as <-.
intros k Hk. assert (k = 0%nat) by lia. subst k. cbn [YP09.c_off] in Hmb. change (Z.of_nat 0) with 0.
rewrite Z.add_0_r. rewrite Z.add_0_r in Hmb. change (ms_mem (restrict H ms)) with (mrestrict H (ms_mem ms)) in Hmb.
rewrite Hmb. f_equal.
rewrite hm_le_byte_1 by lia. apply bv_eq. unfold byte_of_word. cbn [sv_denot]. change (8 * 0) with 0.
rewrite Z.shiftr_0_r. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
change (bv_modulus 8) with 256. rewrite <- Hz. rewrite Z.mod_mod by lia.
rewrite (Z.div_mod z (2 ^ 64)) at 2 by lia. rewrite Z.add_comm.
replace (2 ^ 64 * (z / 2 ^ 64)) with ((2 ^ 56 * (z / 2 ^ 64)) * 256) by ring. rewrite Z.mod_add by lia. reflexivity.
Qed.
End h.

(* ---- the env's values ---- *)
Lemma pa_k_env : forall (regs : bvmap 5 word) R pp plen sel seen,
getr regs 9 = w64 R -> getr regs 10 = w64 plen -> getr regs 11 = w64 sel ->
getr regs 12 = w64 (plen - 0x3ffd) -> getr regs 25 = w64 seen ->
0 <= R < 2 ^ 64 -> 0 <= pp -> pp + 19744 < 2 ^ 64 -> 0 <= plen <= 5424 -> 0 <= sel < 256 -> 0 <= seen <= 1 ->
let E := Ereg regs (pa_extra (pa_k_x pp plen sel)) in
bv_unsigned (ew E 9) = R /\ bv_unsigned (ew E 36) = pp /\ bv_unsigned (ew E 10) = plen /\
bv_unsigned (ew E 11) = sel /\ bv_unsigned (ew E 25) = seen /\ bv_unsigned (ew E 32) = SHADOW_OFF /\
bv_unsigned (ew E 33) = pp + plen /\ bv_unsigned (ew E 34) = sel mod 4 /\
bv_unsigned (ew E 12) = plen - 16381 + 2 ^ 64 /\ bv_unsigned (ew E 35) = plen - 16377 + 2 ^ 64.
Proof.
intros regs R pp plen sel seen H9 H10 H11 H12 H25 HR Hpp0 Hpp1 Hp Hs Hn E.
assert (W : forall z, - 2 ^ 64 <= z < 0 -> bv_unsigned (Z_to_bv 64 z) = z + 2 ^ 64).
{ intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  symmetry. apply (Z.mod_unique z (2 ^ 64) (-1)); lia. }
subst E. repeat match goal with |- _ /\ _ => split end.
- rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), H9. unfold w64. apply unsigned_lit_small. lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 36) with (Z_to_bv 64 pp). apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl), H10. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl), H11. unfold w64. apply unsigned_lit_small. lia.
- rewrite (ew_Ereg_nat regs _ 25 25%bv eq_refl), H25. unfold w64. apply unsigned_lit_small. lia.
- rewrite pa_extra_K. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 33) with (Z_to_bv 64 (pp + plen)). apply unsigned_lit_small. lia.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 34) with (Z_to_bv 64 (sel mod 4)).
  apply unsigned_lit_small. pose proof (Z.mod_pos_bound sel 4 ltac:(lia)). lia.
- rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl), H12. unfold w64. rewrite W by lia. reflexivity.
- change (ew (Ereg regs (pa_extra (pa_k_x pp plen sel))) 35) with (Z_to_bv 64 (plen - 16377)). rewrite W by lia. reflexivity.
Qed.


(* ---- the walk's plumbing for this block ---- *)
(* the write right of a window: the slots R+0xa8 / R+0xc0 / R+0xe8 lie in the caller's stack window; pp's block was made
   since the journal's start (lib/A/HPgBase.v hd_fresh_awr) *)
Ltac pa_k_awr_stk := idtac; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; left; lia.
Ltac pa_k_awr_pp := idtac; let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
lazymatch goal with Hin : In (?p, Layout.PP_SIZE) _, Hout : ~ In (?p, Layout.PP_SIZE) _ |- _ =>
replace a with (p + (a - p)) by lia;
apply (hd_fresh_awr _ _ _ _ _ _ _ p Layout.PP_SIZE); [exact Hin | exact Hout | change (req_size Layout.PP_SIZE) with 19744; lia]
end.
Ltac pa_k_awr :=
lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
repeat first
[ apply awr_ok_nil
| apply awr_ok_cons_ro; [cbn; lia|]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat); [reflexivity | eassumption | pa_k_awr_stk | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 36%nat); [reflexivity | eassumption | pa_k_awr_pp | ]
| eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat); [reflexivity | eassumption | pa_k_awr_pp | ] ].
(* every write window lies in the block's write set *)
Ltac pa_k_kwr :=
idtac; let a := fresh "a" in let r := fresh "r" in let Hr := fresh "Hr" in let Hb := fresh "Hb" in
intros a (r & Hr & Hb); cbv beta;
lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end;
repeat (destruct Hr as [<- | Hr];
  [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hb;
   lazymatch goal with U9 : bv_unsigned (ew _ 9) = _, U36 : bv_unsigned (ew _ 36) = _, U33 : bv_unsigned (ew _ 33) = _ |- _ =>
   rewrite ?U9, ?U36, ?U33 in Hb end; lia | ]);
destruct Hr.
Ltac pa_k_run stop :=
lazymatch goal with HS : st_ok _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok pa_tbl_ok HS HJ SHOK PAspan stop; [pa_k_awr | ] end.
(* the leaf: the post's first eight clauses (lib/A/HPgPropKit.v pa_leaf), with the registers kept against the entry
   state's registers (s4, s5, s7 hold their values as expressions of pp's slot 36 and K) *)
Ltac pa_k_leaf :=
lazymatch goal with
| HS : st_ok _ ?E _ (restrict (w_H ?W) ?ms), HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ ?lyc ?Sc _ _ _ _,
  HRO : regs_ok ?E pa_k_regs ?regs, KE : forall a, _ -> ~ _ -> aview _ _ _ a = _ |- _ =>
apply SRr_ret;
red; exists lyc, Sc, (ms_regs ms), (ms_mem ms); eexists;
split; [rewrite (st_ok_restrict_mkst rsegs (w_H W) _ _ ms HS eq_refl) at 1; reflexivity|];
split; [exact HJ|];
split; [apply (pa_k_regs_kept _ _ ms pa_k_regs regs (w_H W) _ HS HRO); vm_compute; reflexivity|];
split; [reflexivity|];
split; [apply Permutation_refl|];
split; [let rec kio := first [apply same_io_refl | eapply same_io_trans; [| apply same_io_wvb]; kio] in kio|];
split; [apply mo_le_refl; assumption|];
split; [intros a Ha Hz; exact (KE a Ha Hz)|]
end.
(* the value of an 8-byte cell / the bytes of a region at the end of the run *)
Ltac pa_k_val := first [ reflexivity | (erewrite pa_k_soff by eassumption; f_equal; lia) ].
Ltac pa_k_slot_tac n b o Ub :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
let r := eval vm_compute in (pa_k_find n (ss_mem ss) o) in
lazymatch r with Some ?e =>
apply (pa_k_slot E ss ms H n b o e); [exact HS | vm_compute; reflexivity | exact Ub | pa_k_val | lia]
end end.
Ltac pa_k_bytes_tac n b Ub :=
lazymatch goal with HS : st_ok _ ?E ?ss (restrict ?H ?ms) |- _ =>
apply (pa_k_bytes E ss ms H n b); [exact HS | vm_compute; reflexivity | exact Ub]
end.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* the entry state holds at 0x81514 *)
Lemma pa_k_entry : forall (W : world rsegs) (regs : bvmap 5 word) memc R pp plen sel seen (z3 b4 : bool),
getr regs 9 = w64 R -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 SHADOW_OFF ->
getr regs 10 = w64 plen -> getr regs 11 = w64 sel -> getr regs 12 = w64 (plen - 0x3ffd) -> getr regs 25 = w64 seen ->
70368744177664 <= R -> R + 0x110 <= 140737488355328 -> R mod 16 = 0 ->
pp mod 16 = 0 -> 4096 <= pp -> pp <= 140737479946976 -> pp + 19744 <= R ->
(forall o, 0xa8 <= o < 0xf0 -> apresent (w_H W) memc (R + o)) ->
(forall o, 0 <= o < 19744 -> apresent (w_H W) memc (pp + o)) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 (2 ^ 64 - 0x4001) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x50) 8 0x10003 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 0x80001 ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen <= 5424 -> 0 <= sel < 256 -> 0 <= seen <= 1 ->
(sel mod 4 =? 0) = z3 -> Z.testbit sel 4 = b4 ->
regs_ok (Ereg regs (pa_extra (pa_k_x pp plen sel))) pa_k_regs regs /\
st_ok rsegs (Ereg regs (pa_extra (pa_k_x pp plen sel))) (ss_key z3 b4 seen)
  (restrict (w_H W) (mkst regs (Z_to_bv 64 PA_SELK) memc (seg_rom rsegs))).
Proof.
intros W regs memc R pp plen sel seen z3 b4 H9 H21 H20 H23 H10 H11 H12 H25 HR0 HR1 HR16 Hpp16 Hpp0 Hpp1 HppR HpR Hppp
  Vpp Ve0 Ve8 V50 V70 Vlen Hp Hs Hn Hz3 Hb4.
destruct (pa_k_env regs R pp plen sel seen H9 H10 H11 H12 H25 ltac:(lia) ltac:(lia) ltac:(lia) Hp Hs Hn)
  as (U9 & U36 & U10 & U11 & U25 & U32 & U33 & U34 & U12 & U35).
set (E := Ereg regs (pa_extra (pa_k_x pp plen sel))) in *.
assert (HRO : regs_ok E pa_k_regs regs).
{ unfold pa_k_regs.
  apply pa_k_override; [| reflexivity |].
  2:{ rewrite H23, (pa_k_soff E 32 0 SHADOW_OFF U32), Z.add_0_r. reflexivity. }
  apply pa_k_override; [| reflexivity |].
  2:{ rewrite H21, (pa_k_soff E 36 16384 pp U36). reflexivity. }
  apply pa_k_override; [apply regs_ok_Ereg | reflexivity |].
  rewrite H20. apply bv_eq.
  change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 16384) (SLit 3)) (SOff 32 0))))
    with (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 36 16384) (SLit 3)) (SOff 32 0))).
  rewrite U_SAlu, U_srl3. cbn [zalu_raw]. rewrite !U_SOff, U36, U32.
  rewrite (zcanon_id (pp + 16384)) by (unfold M64; lia). rewrite (zcanon_id (SHADOW_OFF + 0)) by (unfold M64, SHADOW_OFF; lia).
  assert (Hd : 0 <= (pp + 16384) / 8 <= pp + 16384) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  unfold w64, shadow_addr. rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia).
  rewrite zcanon_id by (unfold M64, SHADOW_OFF; lia). lia. }
split; [exact HRO|].
unfold ss_key. rewrite restrict_mkst_fx. apply (entry_st_ok_full rsegs).
- exact HRO.
- vm_compute. reflexivity.
- unfold pa_k_mem. repeat apply Forall_cons; try apply Forall_nil.
  + apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * eapply pa_chunk8; [reflexivity | lia | exact V50].
    * eapply pa_chunk8; [reflexivity | lia | exact V70].
  + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply HpR; lia | apply Forall_nil].
  + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply HpR; lia | apply Forall_nil].
  + apply (hm_rw_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia | intros o Ho; apply HpR; lia | apply Forall_nil].
  + apply (hm_ro_region rsegs E (w_H W) memc 9 R); [exact U9 | lia | lia |].
    repeat apply Forall_cons; try apply Forall_nil.
    * eapply pa_chunk8; [rewrite (pa_k_soff E 36 0 pp U36), Z.add_0_r; reflexivity | lia | exact Vpp].
    * eapply pa_chunk8; [ | | exact Ve0]; [apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | lia].
    * eapply pa_chunk8; [ | | exact Ve8]; [apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity | lia].
  + apply (hm_rw_region rsegs E (w_H W) memc 36 pp); [exact U36 | lia | lia | intros o Ho; apply Hppp; lia |].
    apply Forall_cons; [|apply Forall_nil].
    eapply pa_chunk8; [rewrite (pa_k_soff E 10 0 plen U10), Z.add_0_r; reflexivity | lia | exact Vlen].
  + apply (hm_rw_region rsegs E (w_H W) memc 33 (pp + plen)); [exact U33 | lia | lia | | apply Forall_nil].
    intros o Ho. replace (pp + plen + o) with (pp + (plen + o)) by lia. apply Hppp. lia.
- unfold pa_k_mem. change (Ereg regs (pa_extra (pa_k_x pp plen sel))) with E. clearbody E.
  cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U9, U36, U33.
  repeat match goal with |- _ /\ _ => split | |- True => exact I end; lia.
- unfold pa_k_facts, facts_ok. change (Ereg regs (pa_extra (pa_k_x pp plen sel))) with E. clearbody E.
  cbn [f_atoms f_conds f_alias]. split; [|split; [exact I|]].
  + apply pa_k_atoms_app.
    * unfold pa_k_atoms. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U9, U36, U32, U10, U11, U25, U33, U12, U35.
      repeat match goal with |- _ /\ _ => split | |- True => exact I end;
      first [ (change (2 ^ 0) with 1; apply Z.mod_1_r) | (change (2 ^ 4) with 16; lia) | (unfold SHADOW_OFF; lia) | lia ].
    * destruct z3; cbn [pa_k_ex atoms_ok]; [exact I|]. split; [|exact I].
      unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U34. apply Z.eqb_neq in Hz3.
      pose proof (Z.mod_pos_bound sel 4 ltac:(lia)).
      split; [lia|]. split; [change (2 ^ 0) with 1; apply Z.mod_1_r | lia].
  + apply pa_k_alias_app.
    * unfold pa_k_al0. cbn [alias_ok]. split; [|split; [|exact I]].
      -- apply bv_eq.
         change (bv_unsigned (sv_denot E (SAlu ALU_ADD (SOff 36 0) (SOff 10 0)))) with (U E (SAlu ALU_ADD (SOff 36 0) (SOff 10 0))).
         rewrite U_add_off_atom by (rewrite ?U36, ?U10; unfold M64; lia). rewrite U36, U10.
         rewrite (pa_k_soff E 33 0 (pp + plen) U33). rewrite unsigned_lit_small by lia. lia.
      -- rewrite (pa_k_soff E 10 (-16377) plen U10), (pa_k_soff E 35 0 _ U35). apply bv_eq. rewrite !Z_to_bv_unsigned.
         unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r.
         replace (plen - 16377 + 2 ^ 64) with ((plen + -16377) + 1 * 2 ^ 64) by ring. rewrite Z.mod_add by lia. reflexivity.
    * destruct z3, b4; cbn [pa_k_al alias_ok]; (split; [|split; [|exact I]]);
      (rewrite (pa_k_and_lit E 11 sel _ U11) by lia);
      first [ (rewrite pa_k_land16, Hb4; reflexivity)
            | (rewrite pa_k_land3; first [ (apply Z.eqb_eq in Hz3; rewrite Hz3; reflexivity)
                                         | (rewrite (pa_k_soff E 34 0 _ U34), Z.add_0_r; reflexivity) ]) ].
Qed.

Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis LAWS : AR_laws rsegs B.
Local Notation pa_post := (pa_post B MT).

(* the shadow entries: the bytes of pp's block and the 16 bytes from pp + len are addressable, outside the band *)
Lemma pa_k_shok : forall ly S W mem md E pp plen,
AR rsegs B ly S W mem md -> In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
bv_unsigned (ew E 32) = SHADOW_OFF -> bv_unsigned (ew E 36) = pp -> bv_unsigned (ew E 33) = pp + plen ->
0 <= plen -> plen + 16 <= 19744 -> 4096 <= pp -> pp + 19744 <= 140737479966720 -> in_app pp 19744 ->
sh_ok rsegs PABx pa_k_SH E (mrestrict (w_H W) mem).
Proof using LAWS.
intros ly S W mem md E pp plen HAR Hin U32 U36 U33 Hp0 Hp1 Hpp0 Hpp1 Happ.
assert (UB : U E PABx = SHADOW_OFF) by (unfold PABx; rewrite U_SOff, U32, Z.add_0_r; apply zcanon_id; unfold SHADOW_OFF, M64; lia).
assert (HAP : forall a, pp <= a < pp + 19744 -> ~ (U E PABx <= a < U E PABx + 17592186044416)).
{ intros a Ha. rewrite UB. unfold in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
assert (V36 : U E (SOff 36 0) = pp) by (rewrite U_SOff, U36, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (V33 : U E (SOff 33 0) = pp + plen) by (rewrite U_SOff, U33, Z.add_0_r; apply zcanon_id; unfold M64; lia).
constructor; [|constructor; [|constructor]]; split; cbn [she_m she_lo she_hi].
- rewrite V36. eapply (obl_of_block rsegs B LAWS); [exact HAR | exact Hin | exact UB | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite V36 in Ha. apply HAP. lia.
- rewrite V33. eapply (obl_of_block rsegs B LAWS); [exact HAR | exact Hin | exact UB | lia | change (req_size Layout.PP_SIZE) with 19744; lia].
- unfold app_apart. cbn [she_m she_lo she_hi]. intros a Ha. rewrite V33 in Ha. apply HAP. lia.
Qed.

(* ---- the key block 0x81514 -> 0x8165c (params Struct) / 0x82808 (Int 7) ---- *)
Lemma pa_key : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (R pp plen sel seen : Z),
ajournal rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 9 = w64 R -> getr regs 21 = w64 (pp + 0x4000) ->
getr regs 20 = w64 (shadow_addr (pp + 0x4000)) -> getr regs 23 = w64 SHADOW_OFF ->
getr regs 10 = w64 plen -> getr regs 11 = w64 sel -> getr regs 12 = w64 (plen - 0x3ffd) -> getr regs 25 = w64 seen ->
sp0 - STK + T_SEG_STK <= R -> R + 0x1e0 <= sp0 -> R mod 16 = 0 ->
In (pp, Layout.PP_SIZE) (ablocks B lyc Sc) -> ~ In (pp, Layout.PP_SIZE) (ablocks B ly S) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0xf0) 8 pp ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x100) 8 (2 ^ 64 - 0x4001) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x108) 8 (2 ^ 64 - 0x3ffd) ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x50) 8 0x10003 ->
val_mem rsegs (mrestrict (w_H W) memc) (R + 0x70) 8 0x80001 ->
val_mem rsegs (mrestrict (w_H W) memc) (pp + 0x4000) 8 plen ->
0 <= plen -> plen + 16 <= 5440 -> 0 <= sel < 256 -> (seen = 0 \/ seen = 1) ->
SRr rsegs W (cfg_at rsegs PA_SELK regs memc mdc)
(pa_post STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc
 (if (sel mod 4 =? 0) || Z.testbit sel 4 then PA_SELI else PA_SELS)
 [10; 11; 12; 13; 14; 15]%bv
 (fun a => pp + plen <= a < pp + plen + 8 \/ pp + 0x4000 <= a < pp + 0x4008 \/
           R + 0xa8 <= a < R + 0xb0 \/ R + 0xc0 <= a < R + 0xc8 \/ R + 0xe8 <= a < R + 0xf0)
 (fun W2 regs2 mem2 =>
   getr regs2 10 = w64 (plen + 8 - 0x3ffd) /\
   garr8 rsegs (mrestrict (w_H W2) mem2) (pp + plen)
     (map (fun x : byte => bv_unsigned x) (Cursor.le32 (if sel mod 4 =? 0 then 0x10003 else 0x80001) ++ Cursor.le32 0)) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (pp + 0x4000) 8 (plen + 8) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xa8) 8 (if sel mod 4 =? 0 then seen else 1) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xe8) 8 (if (sel mod 4 =? 0) || (seen =? 1) then 0 else 1) /\
   val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0xc0) 8 (plen + 8))).
Proof using MTL LAWS.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs R pp plen sel seen HJ H9 H21 H20 H23 H10 H11 H12 H25
  HRlo HRhi HR16 Hin Hout Vpp Ve0 Ve8 V50 V70 Vlen Hp0 Hp16 Hsel Hseen.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof YM05.alloc_ceiling_val as (ACV & _).
pose proof (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hpp16 & Hpp4k & Hppc & Happ & Hppres & _).
change (req_size Layout.PP_SIZE) with 19744 in Hppc, Happ, Hppres.
unfold T_SEG_STK, ASTACK in HRlo.
assert (HpR : forall o, 0xa8 <= o < 0xf0 -> apresent (w_H W) memc (R + o)) by (intros o Ho; apply Hpres; lia).
assert (Hppp : forall o, 0 <= o < 19744 -> apresent (w_H W) memc (pp + o)) by (intros o Ho; apply (Hppres (pp + o)); lia).
assert (Hpp' : pp <= 140737479946976) by lia.
assert (Hppc' : pp + 19744 <= 140737479966720) by lia.
destruct (sel mod 4 =? 0) eqn:Hz3; destruct (Z.testbit sel 4) eqn:Hb4; destruct Hseen as [Hs | Hs]; subst seen;
cbv beta iota delta [orb Z.eqb Pos.eqb].
all: pose proof (pa_k_entry W regs memc R pp plen sel _ _ _ H9 H21 H20 H23 H10 H11 H12 H25 ltac:(lia) ltac:(lia) HR16
  Hpp16 Hpp4k Hpp' ltac:(lia) HpR Hppp Vpp Ve0 Ve8 V50 V70 Vlen ltac:(lia) ltac:(lia) ltac:(lia) Hz3 Hb4) as [HRO HS].
all: destruct (pa_k_env regs R pp plen sel _ H9 H10 H11 H12 H25 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
  as (U9 & U36 & U10 & U11 & U25 & U32 & U33 & U34 & U12 & U35).
all: pose proof (pa_k_shok lyc Sc W memc mdc (Ereg regs (pa_extra (pa_k_x pp plen sel))) pp plen HAR Hin U32 U36 U33 ltac:(lia) ltac:(lia) Hpp4k Hppc' Happ) as SHOK.
all: remember (Ereg regs (pa_extra (pa_k_x pp plen sel))) as E eqn:HE.
all: clear HE.
all: assert (KE : forall a, 0 <= a < 2 ^ 64 ->
  ~ (pp + plen <= a < pp + plen + 8 \/ pp + 0x4000 <= a < pp + 0x4008 \/
     R + 0xa8 <= a < R + 0xb0 \/ R + 0xc0 <= a < R + 0xc8 \/ R + 0xe8 <= a < R + 0xf0) ->
  aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a) by (intros; reflexivity).
all: unfold cfg_at; change (w64 PA_SELK) with (Z_to_bv 64 PA_SELK).
all: lazymatch goal with |- context [HPgPropKit.pa_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?pc _ _ _] => pa_k_run pc end.
all: pa_keep pa_k_kwr.
all: pa_k_leaf.
all: cbv beta.
all: split; [pa_reg (10%bv : bv 5); rewrite (pa_k_soff _ 10 _ plen U10); unfold w64; f_equal; lia|].
all: split; [pa_k_bytes_tac 33%nat (pp + plen) U33|].
all: split; [pa_k_slot_tac 36%nat pp 16384 U36|].
all: split; [pa_k_slot_tac 9%nat R 168 U9|].
all: split; [pa_k_slot_tac 9%nat R 232 U9|].
all: pa_k_slot_tac 9%nat R 192 U9.
Qed.
End d.
End b.

Print Assumptions pa_key.
