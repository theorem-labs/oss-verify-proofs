(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: cgif_file_fuzzer lib/A/AE6x.v's proof of the memchr interceptor (entry walk, musl body, shadow check) with AE7d.v's 2144-byte frame and eight saved registers, restated for the strlen interceptor of libreac/fuzz_disco over lib/Rt/StrlenDef.v's contract; module paths. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Rt/Strlen.v, with its module paths, module names and addresses changed; 182 of its 493 lines of code are new or changed and 132 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: relocated from a Theorem Labs lane's cgif_file_fuzzer-coordinate copy (a working branch f8664b31b9c, proofs/cgif/cgif_file_fuzzer/lib/A/FMstrlen.v) to fuzz_identity.asan by an address map recorded by the porting lane; module paths, the record class TfibSyms (unchanged), YA0m import dropped. *)
(* Modified by Theorem Labs, 2026-10-29: for a Theorem Labs lane's acceptance (a working branch), the record class is TfibSyms, not IdentTfibSyms, and the core modules are Required by full path at the applied A core's names (lib/A/A*.v, lib/Reusable/YA0m, YE08, YE21). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/FMstrlen.v, with its module paths and module names changed; 197 of its 249 lines of code are new or changed and 441 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMstrlen.v at 6ebe35ba632; the entry and
   epilogue symbolic states of the strlen walk are replaced by the three symbolic states of the strcspn wrapper's
   walk from its trampoline to 0x42d38 (the wrapper prologue up to musl __strchrnul's loops, and the state the
   loops return to), with the state readers and the byte-level helpers those states need. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE34
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0l
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0m
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AF0x
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AB1w
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE20
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE2y
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A.AE3a.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import FMcs0.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The addresses the walk's three symbolic phases start and stop at, and the three byte loads the walk names:
   0x91890 / 0x9189c read the set's two bytes inside musl strcspn, 0x63ce8 is the byte load of the runtime's
   internal_strlen (it runs twice over the same two bytes). 0x5f45d8 is the stack guard, an image address; the
   return address musl strcspn hands __strchrnul is 0x9193c. *)
Definition CS_GUARD : Z := 0x5f45d8.
Definition CS_CN_RA : Z := 0x9193c.
Definition A_LB1 : Z := 0x91890.
Definition A_LB2 : Z := 0x9189c.
Definition A_SLB : Z := 0x63ce8.
Definition W_LB1 : Z := 0x0004c583.
Definition W_LB2 : Z := 0x0014c503.
Definition W_SLB : Z := 0x00064603.

(* ---------------------------------------------------------------- the three symbolic phases *)
Definition stkE : YP09.region := YP09.mkRegion (Some 2%nat) (- CS_WIN) 0 (- CS_WIN) 0 [].
Definition grdR : YP09.region :=
YP09.mkRegion None CS_GUARD (CS_GUARD + 8) 0 0 [YP09.mkChunk CS_GUARD (CVal 8 (SOff 32 0))].
Definition factsE : list (nat * afact) := [(2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (33%nat, mkAF 1 255 0)].
Definition ssE : sstate :=
mkSS CS_ENTRY sr_atoms (stkE :: grdR :: map ro_region cs_rodata) None (mkFacts factsE [] []).
Definition RT (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_cs FUEL stop s.

Definition e1 : sstate := Eval vm_compute in fst (RT A_LB1 ssE).
Lemma r_e1 : RT A_LB1 ssE = (e1, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition s1b : sstate := set_regs_pc e1 [((11%bv : bv 5), SOff 33 0)] (A_LB1 + 4).
Definition e2 : sstate := Eval vm_compute in fst (RT A_LB2 s1b).
Lemma r_e2 : RT A_LB2 s1b = (e2, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition s1c : sstate := set_regs_pc e2 [((10%bv : bv 5), SLit 0)] (A_LB2 + 4).
Definition cs_cmask : sv := SAlu ALU_AND (SOff 33 0) (SLit 255).
Definition e3 : sstate := Eval vm_compute in fst (RT CS_LOOP s1c).
Lemma r_e3 : RT CS_LOOP s1c = (e3, RS_stopped (SR_branch BC_EQ cs_cmask (SLit 0))).
Proof. vm_compute. reflexivity. Qed.
Definition s1d : sstate := add_cond e3 (mkAC BC_NE cs_cmask (SLit 0)).
Definition e4 : sstate := Eval vm_compute in fst (RT CS_LOOP s1d).
Lemma r_e4 : RT CS_LOOP s1d = (e4, RS_running). Proof. vm_compute. reflexivity. Qed.

(* the state __strchrnul's loops return to: the stack words the epilogues reload (__strchrnul's ra and s0, musl
   strcspn's ra, s0 .. s3 and its copy of the guard), the guard cell and the const cells *)
Definition stk3 : YP09.region := YP09.mkRegion (Some 2%nat) 0 96 0 0
[YP09.mkChunk 0 (CVal 8 (SOff 34 0)); YP09.mkChunk 8 (CVal 8 (SLit CS_CN_RA));
 YP09.mkChunk 48 (CVal 8 (SOff 32 0)); YP09.mkChunk 56 (CVal 8 (SOff 35 0));
 YP09.mkChunk 64 (CVal 8 (SLit 1)); YP09.mkChunk 72 (CVal 8 (SOff 34 0));
 YP09.mkChunk 80 (CVal 8 (SOff 36 0)); YP09.mkChunk 88 (CVal 8 (SLit CS_RET1))].
Definition facts3 : list (nat * afact) := [(2%nat, mkAF (2 ^ 43) (2 ^ 47) 4); (33%nat, mkAF 1 255 0)].
Definition sr3 : list sv := sr_set sr_atoms (18%bv : bv 5) (SLit CS_GUARD).
Definition ss3 : sstate :=
mkSS CS_LOOP_END sr3 (stk3 :: grdR :: map ro_region cs_rodata) None (mkFacts facts3 [] []).
Definition e5 : sstate := Eval vm_compute in fst (RT A_SLB ss3).
Lemma r_e5 : RT A_SLB ss3 = (e5, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition s3b : sstate := set_regs_pc e5 [((12%bv : bv 5), SOff 33 0)] (A_SLB + 4).
Definition e6 : sstate := Eval vm_compute in fst (RT A_SLB s3b).
Lemma r_e6 : RT A_SLB s3b = (e6, RS_running). Proof. vm_compute. reflexivity. Qed.
Definition s3c : sstate := set_regs_pc e6 [((12%bv : bv 5), SLit 0)] (A_SLB + 4).
Definition e7 : sstate := Eval vm_compute in fst (RT CS1_ENTRY s3c).
Lemma r_e7 : RT CS1_ENTRY s3c = (e7, RS_running). Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------- reading the states *)
Definition RGv (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (s : sstate) (r : Z) (v : sv) : bool := sv_eqb (RGv s r) v.
Definition CS_KEEPB : list Z := [3; 4; 20; 24; 25; 26; 27].
Definition chunk_is (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunk (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_is off v) (YP09.r_chunks r) | [] => false end.
Definition win_chk (rs : smem) : bool :=
forallb (fun t => win_eqb t (Some 2%nat, - CS_WIN, 0) || (snd t <=? snd (fst t))) (windows rs).
Definition win_empty (rs : smem) : bool := forallb (fun t => snd t <=? snd (fst t)) (windows rs).

Lemma e1_f : ss_pc e1 = A_LB1 /\ ss_resv e1 = None /\ ss_atoms_lt 34 e1 = true /\
sr_get (ss_regs e1) (9%bv : bv 5) = SOff 11 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma e2_f : ss_pc e2 = A_LB2 /\ ss_resv e2 = None /\ ss_atoms_lt 34 e2 = true /\
sr_get (ss_regs e2) (9%bv : bv 5) = SOff 11 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma e4_f : ss_pc e4 = CS_LOOP /\ ss_resv e4 = None /\
sr_get (ss_regs e4) (10%bv : bv 5) = SOff 10 0 /\ sr_get (ss_regs e4) (11%bv : bv 5) = cs_cmask /\
sr_get (ss_regs e4) (2%bv : bv 5) = SOff 2 (- CS_WIN) /\
sr_get (ss_regs e4) (18%bv : bv 5) = SLit CS_GUARD /\
forallb (fun r => reg_is e4 r (SOff (Z.to_nat r) 0)) CS_KEEPB = true.
Proof. repeat split; vm_compute; reflexivity. Qed.
Definition e4_r0 : YP09.region := Eval vm_compute in match ss_mem e4 with r :: _ => r | [] => stkE end.
Definition e4_rest : smem := Eval vm_compute in match ss_mem e4 with _ :: t => t | [] => [] end.
Lemma e4_mem : ss_mem e4 = e4_r0 :: e4_rest. Proof. vm_compute. reflexivity. Qed.
Lemma e4_r0_f : YP09.r_base e4_r0 = Some 2%nat /\ YP09.r_wlo e4_r0 = - CS_WIN /\ YP09.r_whi e4_r0 = 0.
Proof. repeat split; vm_compute; reflexivity. Qed.

(* the eight stack words the state at __strchrnul's exit reloads, each at its offset below the entry sp *)
Definition CS3C : list (Z * sv) :=
[(- CS_WIN + 0, SOff 10 0); (- CS_WIN + 8, SLit CS_CN_RA); (- CS_WIN + 48, SOff 32 0);
 (- CS_WIN + 56, SOff 11 0); (- CS_WIN + 64, SLit 1); (- CS_WIN + 72, SOff 10 0);
 (- CS_WIN + 80, SOff 2 0); (- CS_WIN + 88, SLit CS_RET1)].
Lemma e4_chunks : forallb (fun p => has_chunk e4 (fst p) (snd p)) CS3C = true.
Proof. vm_compute. reflexivity. Qed.
Lemma e4_saved : forallb (fun p => has_chunk e4 (snd p) (SOff (Z.to_nat (fst p)) 0)) CS_SAVED = true.
Proof. vm_compute. reflexivity. Qed.

Lemma e5_f : ss_pc e5 = A_SLB /\ ss_resv e5 = None /\ ss_atoms_lt 37 e5 = true /\
sr_get (ss_regs e5) (12%bv : bv 5) = SOff 35 0.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma e6_f : ss_pc e6 = A_SLB /\ ss_resv e6 = None /\ ss_atoms_lt 37 e6 = true /\
sr_get (ss_regs e6) (12%bv : bv 5) = SOff 35 1.
Proof. repeat split; vm_compute; reflexivity. Qed.
Lemma e7_f : ss_pc e7 = CS1_ENTRY /\ ss_resv e7 = None /\
sr_get (ss_regs e7) (2%bv : bv 5) = SOff 2 96 /\ sr_get (ss_regs e7) (8%bv : bv 5) = SOff 36 0 /\
sr_get (ss_regs e7) (9%bv : bv 5) = SOff 34 0 /\ sr_get (ss_regs e7) (19%bv : bv 5) = SOff 35 0 /\
sr_get (ss_regs e7) (10%bv : bv 5) = SLit 1 /\ sr_get (ss_regs e7) (23%bv : bv 5) = SLit CS_FLAGS /\
sr_get (ss_regs e7) (21%bv : bv 5) = SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 34 0) (SLit (2 ^ 64 - 1))) /\
forallb (fun r => reg_is e7 r (SOff (Z.to_nat r) 0)) CS_KEEPB = true.
Proof. repeat split; vm_compute; reflexivity. Qed.

Lemma wc_ssE : win_chk (ss_mem ssE) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wc_s1b : win_chk (ss_mem s1b) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wc_s1c : win_chk (ss_mem s1c) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wc_s1d : win_chk (ss_mem s1d) = true. Proof. vm_compute. reflexivity. Qed.
Lemma we_ss3 : win_empty (ss_mem ss3) = true. Proof. vm_compute. reflexivity. Qed.
Lemma we_s3b : win_empty (ss_mem s3b) = true. Proof. vm_compute. reflexivity. Qed.
Lemma we_s3c : win_empty (ss_mem s3c) = true. Proof. vm_compute. reflexivity. Qed.

Lemma clk_lb1 : clookup tbl_cs A_LB1 = Some W_LB1. Proof. vm_compute. reflexivity. Qed.
Lemma clk_lb2 : clookup tbl_cs A_LB2 = Some W_LB2. Proof. vm_compute. reflexivity. Qed.
Lemma clk_slb : clookup tbl_cs A_SLB = Some W_SLB. Proof. vm_compute. reflexivity. Qed.
Lemma dec_lb1 : decode_any (Z_to_bv 32 W_LB1) = Some (Load SZ1 false (11%bv : bv 5) (9%bv : bv 5) (0%bv : bv 12), 4).
Proof. vm_refl_bv. Qed.
Lemma dec_lb2 : decode_any (Z_to_bv 32 W_LB2) = Some (Load SZ1 false (10%bv : bv 5) (9%bv : bv 5) (1%bv : bv 12), 4).
Proof. vm_refl_bv. Qed.
Lemma dec_slb : decode_any (Z_to_bv 32 W_SLB) = Some (Load SZ1 false (12%bv : bv 5) (12%bv : bv 5) (0%bv : bv 12), 4).
Proof. vm_refl_bv. Qed.
Lemma guard_img : zallb (img_byte_ok tfibsegs) CS_GUARD 8%nat = true. Proof. vm_compute. reflexivity. Qed.

(* ---------------------------------------------------------------- byte-level and state helpers *)
Lemma chunk_is_sound : forall off v c, chunk_is off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_is in Hc. cbn [YP09.c_off YP09.c_val] in Hc.
apply andb_prop in Hc as [Ho Hv]. apply Z.eqb_eq in Ho.
destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.
Lemma v_addi_lit : forall z i, v_addi (Z_to_bv 64 z) i = Z_to_bv 64 (z + i).
Proof.
intros z i. apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma mb_same : forall (Hh : word -> bool) (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte tfibsegs (mrestrict Hh m') a = mbyte tfibsegs (mrestrict Hh m) a.
Proof. intros Hh m m' a E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma md_wvb_gen : forall m : Model, m = with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma munrestrict_mrestrict_same : forall (Hh : word -> bool) (m : word -> option byte) z,
munrestrict Hh m (mrestrict Hh m) z = m z.
Proof. intros Hh m z. unfold munrestrict, mrestrict. destruct (Hh z); reflexivity. Qed.
Lemma rdn1_mbyte : forall (m : word -> option byte) a,
rdn tfibsegs m (Z_to_bv 64 a) 1 = match mbyte tfibsegs m a with Some b => Some [b] | None => None end.
Proof.
intros m a. cbn [rdn].
change (match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom tfibsegs (Z_to_bv 64 a) end)
with (mbyte tfibsegs m a).
destruct (mbyte tfibsegs m a); reflexivity.
Qed.
Lemma nth_map_app_nul : forall (l : list byte) j, (j <= length l)%nat ->
Z_to_bv 8 (nth j (map (fun b : byte => bv_unsigned b) l ++ [0]) 0) = nth j (l ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).
Proof.
induction l as [|b l IH]; intros j Hj.
- destruct j as [|j]; cbn in Hj |- *; [reflexivity | lia].
- destruct j as [|j]; cbn [length map app nth] in Hj |- *.
  + apply Z_to_bv_bv_unsigned.
  + apply IH. cbn in Hj. lia.
Qed.
Lemma garr8_av : forall (Hh : word -> bool) (m : word -> option byte) base l j,
garr8 tfibsegs (mrestrict Hh m) base l -> (j < length l)%nat ->
aview tfibsegs Hh m (base + Z.of_nat j) = Some (nth j l 0).
Proof.
intros Hh m base l j Hg Hj. destruct (Hg j Hj) as (Hv & Hr).
specialize (Hv 0%nat ltac:(lia)). rewrite Z.add_0_r in Hv.
unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite le_byte_small by (change (2 ^ (8 * Z.of_nat 1)) with 256; lia).
cbn [Nat.mul Z.of_nat Z.mul]. rewrite Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma img_byte_some : forall (Hh : word -> bool) (m : word -> option byte) a,
img_byte_ok tfibsegs a = true -> exists v, aview tfibsegs Hh m a = Some v /\ 0 <= v < 256.
Proof.
intros Hh m a Hi. unfold aview, mbyte. destruct (mrestrict Hh m (Z_to_bv 64 a)) as [b|].
- exists (bv_unsigned b). split; [reflexivity|]. pose proof (u8_range b). lia.
- unfold img_byte_ok, img_byte in Hi. destruct (seg_rom tfibsegs (Z_to_bv 64 a)) as [b|]; [|discriminate].
  exists (bv_unsigned b). split; [reflexivity|]. pose proof (u8_range b). lia.
Qed.
(* the stack guard is an image address: every memory reads it *)
Lemma guard_word : forall (Hh : word -> bool) (m : word -> option byte),
exists g, val_mem tfibsegs (mrestrict Hh m) CS_GUARD 8 g /\ 0 <= g < 2 ^ 64.
Proof.
intros Hh m.
assert (B : forall k, 0 <= k < 8 -> exists v, aview tfibsegs Hh m (CS_GUARD + k) = Some v /\ 0 <= v < 256)
by (intros k Hk; apply img_byte_some; exact (zallb_sound _ _ _ (CS_GUARD + k) guard_img ltac:(lia))).
destruct (B 0 ltac:(lia)) as (v0 & E0 & R0). destruct (B 1 ltac:(lia)) as (v1 & E1 & R1).
destruct (B 2 ltac:(lia)) as (v2 & E2 & R2). destruct (B 3 ltac:(lia)) as (v3 & E3 & R3).
destruct (B 4 ltac:(lia)) as (v4 & E4 & R4). destruct (B 5 ltac:(lia)) as (v5 & E5 & R5).
destruct (B 6 ltac:(lia)) as (v6 & E6 & R6). destruct (B 7 ltac:(lia)) as (v7 & E7 & R7).
rewrite Z.add_0_r in E0.
assert (RW : exists v, rdword (aview tfibsegs Hh m) CS_GUARD = Some v /\ 0 <= v < 2 ^ 64).
{ unfold rdword. rewrite E0, E1, E2, E3, E4, E5, E6, E7. eexists. split; [reflexivity|]. lia. }
destruct RW as (g & Hg & Hr). exists g. split; [apply val_mem_of_rdword; exact Hg | exact Hr].
Qed.
Section w. Context {fx : YK11.FPState}.
Lemma chunk_of_st : forall (Hh : word -> bool) E ss ms r0 rest off v,
st_ok tfibsegs E ss (restrict Hh ms) -> ss_mem ss = r0 :: rest -> has_chunk ss off v = true ->
YP09.chunk_ok tfibsegs E (mrestrict Hh (ms_mem ms)) (base_val E (YP09.r_base r0))
(YP09.mkChunk off (CVal 8 v)).
Proof.
intros Hh E ss ms r0 rest off v HS Hmem Hc. unfold has_chunk in Hc. rewrite Hmem in Hc.
apply existsb_exists in Hc as (ck & Hin & Hck). apply chunk_is_sound in Hck. subst ck.
pose proof (st_ok_mem_ok tfibsegs E ss _ HS) as (_ & Hrs & _).
cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
exact (proj1 (Forall_forall _ _) Hcs _ Hin).
Qed.
End w.
Lemma chunk_xfer : forall (Hh : word -> bool) E E' (m m' : word -> option byte) base base' off off' (v v' : sv),
YP09.chunk_ok tfibsegs E (mrestrict Hh m) base (YP09.mkChunk off (CVal 8 v)) ->
sv_denot E' v' = sv_denot E v -> base' + off' = base + off -> (forall z, m' z = m z) ->
YP09.chunk_ok tfibsegs E' (mrestrict Hh m') base' (YP09.mkChunk off' (CVal 8 v')).
Proof.
intros Hh E E' m m' base base' off off' v v' Hok Hv Hb Hm i Hi.
cbn [YP09.c_off YP09.c_val YP09.c_len YP09.cv_len] in *.
destruct (Hok i Hi) as (b & H1 & H2). exists b. split.
- cbn [YP09.cbyte] in H1 |- *. rewrite Hv. exact H1.
- rewrite (mb_same Hh m m' (base' + off' + i) (Hm _)). rewrite Hb. exact H2.
Qed.
Lemma win_empty_no_wrange : forall E rs a, win_empty rs = true -> ~ in_wrange E rs a.
Proof.
intros E rs a Hw Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Ht & Hr).
unfold win_empty in Hw. rewrite forallb_forall in Hw. specialize (Hw _ Ht). cbn [fst snd] in Hw.
apply Z.leb_le in Hw. lia.
Qed.
Lemma frame_all : forall E rs (m m1 : word -> option byte), win_empty rs = true ->
frame_of E rs m m1 -> forall z, m1 z = m z.
Proof. intros E rs m m1 Hw HF z. apply HF. apply win_empty_no_wrange. exact Hw. Qed.
