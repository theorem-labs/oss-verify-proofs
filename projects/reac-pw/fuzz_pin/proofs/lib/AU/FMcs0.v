(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-29: relocated from libreac/fuzz_grant (a working branch 97c611eec86,
   proofs/libreac/fuzz_grant/lib/A/Rt/StrcmpTbl.v, owner a Theorem Labs lane) to libreac/fuzz_identity's ASan build (image A)
   by an address map recorded by the porting lane; module paths, GrantSyms ->
   TfibSyms, and scmp_ranges now states the trampoline word itself (see below). The proofs are a Theorem Labs lane's,
   unchanged. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Rt/StrcmpTbl.v, with its module paths and module names changed; 155 of its 251 lines of code are new or changed and 29 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_identity/lib/A/FMsl0.v and lib/A/FMstrlen_chk1.v (sl_ld8) at 6ebe35ba632; the table holds the strcspn wrapper body, musl __strchrnul and musl strcspn of reac-pw/fuzz_pin.asan, the load lemmas read one byte as well as eight, and the interfaces of the pieces of the strcspn walk are stated here. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/FMcs0.v of this library, for reac-pw/fuzz_pin's asan-ubsan image (fuzz_pin.asan-ubsan d6f83d301522) instead of its asan image (fuzz_pin.asan 3e4859aed23f): module paths lib.A -> lib.AU (the core files A<xyz> -> Y<xyz>); lib.A.PPgWrap, image-independent, kept; 27 address numerals moved to the same symbol + offset of the asan-ubsan image (each checked on that image); by hand, comments only: the address list names fuzz_pin.asan-ubsan (sha256 d6f83d301522, unstripped twin 635d02c7e8fa), the core files YE34 / YE2y / lib/AU/YF0m.v, and the pieces' files under lib/AU. The comment lines above describe how lib/A/FMcs0.v was made and quote the asan image's values; the code and comments below carry the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
Require Import
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YB1v
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YE34
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YF0l
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YF0m
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YF0x
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YB1w
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YE20
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YE2y
  OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.YE3a.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN01.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require PPgWrap.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* The addresses of the strcspn walk in fuzz_pin.asan-ubsan (sha256 d6f83d301522; symbol names from the unstripped
   twin 635d02c7e8fa):
     0x4191c  the 4-byte trampoline `j 0x42cb8` (not in YE34's trampoline ranges, so tbl_cs adds its one word)
     0x42cb8  the wrapper body, 290 words to 0x43140; its frame is 0x7f0 + 0x80 = 2160 bytes
     0x42d10  the return address of the call of musl strcspn through the slot 0x9ae90
     0x42d38  the return address of the call of the runtime's internal_strlen 0x63ce0 on the set: the range check of
              the set [y, y + 2) begins here and ends at 0x42d88
     0x42d88  the range check of the string [x, x + r + 1) begins here (strict_string_checks byte 0x13331d = 0)
              and ends at 0x42de0, the epilogue
     0x91970  musl strcspn, 70 words (frame 0x50, stack guard copy at sp + 0x20)
     0x91858  musl __strchrnul, 56 words (frame 0x10); 0x9186c is its first instruction after the c = 0 test, 0x91928
              its epilogue.
   The deepest stack the walk uses is 2160 + 80 + 16 = 2256 bytes below the caller's sp (in __strchrnul); the range
   check of the string uses 2160 + 72. *)
Definition CS_ENTRY : Z := 0x4191c.
Definition CS_BODY : Z := 0x42cb8.
Definition CS_RET1 : Z := 0x42d10.
Definition CS1_ENTRY : Z := 0x42d38.
Definition CS1_END : Z := 0x42d88.
Definition CS2_ENTRY : Z := 0x42d88.
Definition CS2_END : Z := 0x42de0.
Definition CS_MUSL : Z := 0x91970.
Definition CS_CHRNUL : Z := 0x91858.
Definition CS_LOOP : Z := 0x9186c.
Definition CS_LOOP_END : Z := 0x91928.
Definition CS_FRAME : Z := 2160.
Definition CS_WIN : Z := 2256.
Definition CHK_SCR : Z := 72.
Definition CS_FLAGS : Z := 0x133228.

Definition cs_ranges : list (Z * nat) := [(0x4191c, 1%nat); (0x42cb8, 290%nat); (0x91858, 56%nat); (0x91970, 70%nat)].
Definition tbl_cs : ctable := Eval vm_compute in build_ranges cs_ranges tbl_icpt.
Lemma tbl_cs_eq : tbl_cs = build_ranges cs_ranges tbl_icpt.
Proof. vm_cast_no_check (eq_refl tbl_cs). Qed.
Lemma tbl_cs_ok : table_ok tfibsegs tbl_cs.
Proof.
rewrite tbl_cs_eq. apply build_ranges_ok; [| exact tbl_icpt_ok].
unfold cs_ranges. repeat constructor; cbn; discriminate.
Qed.
(* the trampoline, the first and the last word of the wrapper body, of __strchrnul and of musl strcspn *)
Lemma tbl_cs_probe :
clookup tbl_cs 0x4191c = Some 0x39c0106f /\
clookup tbl_cs 0x42cb8 = Some 0x81010113 /\ clookup tbl_cs 0x4313c = Some 0xca5ff06f /\
clookup tbl_cs 0x91858 = Some 0xff010113 /\ clookup tbl_cs 0x91934 = Some 0x00008067 /\
clookup tbl_cs 0x91970 = Some 0xfb010113 /\ clookup tbl_cs 0x91a84 = Some 0xd71f50ef.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* The read-only cells the walk reads, beyond YE2y's icpt_rodata: the slot of musl strcspn (0x42cfc), the GOT cell
   of the runtime's flags object (0x42d18), the 8-byte cell of the flags object that holds intercept_strspn (byte 7,
   read at 0x42d1c, value 1) and strict_string_checks (byte 5, read at 0x42d88, value 0), and the GOT cell of the
   stack guard (0x91990). Each is a const cell of the start-up (lib/AU/YF0m.v Tfib_const). *)
Definition cs_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0x9ae90, 8, [(0, 8%N, 0x91970)]); (0x99160, 8, [(0, 8%N, 0x133228)]);
(0x133318, 8, [(0, 8%N, 0x101000100000000)]); (0x99df8, 8, [(0, 8%N, 0x5f46d8)])].
Lemma cs_rodata_chk : forall ly, rodata_chk ly cs_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma cs_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_runN tfibsegs tbl_cs FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_cs tbl_cs_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma cs_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) ->
sym_run_toN tfibsegs tbl_cs FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1)
| _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_cs tbl_cs_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|].
split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
(* FMstrlen_chk1.sl_ld8 over tbl_cs: an 8-byte load whose value becomes the atom k *)
Lemma cs_ld8 : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (h : Z) (k K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_cs (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ8 true rd rs 0%bv, 4) ->
bv_eqb rd 0%bv = false ->
sv_denot E (sr_get (ss_regs ss) rs) = Z_to_bv 64 h -> 0 <= h -> h + 8 <= 2 ^ 64 ->
rdword (aview tfibsegs (w_H W) (ms_mem ms)) h = Some (bv_unsigned (ew E k)) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, SOff k 0)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w h k K HS Hrv Hat Hlk Hdec Hrd Hrs Hh0 Hh8 Hw. pose proof YF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_cs_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
pose proof (val_mem_of_rdword (w_H W) (ms_mem ms) h _ Hw) as Hvm.
apply (proj1 (val_mem_word_mem tfibsegs _ _ _)) in Hvm.
destruct (word_mem_ld tfibsegs _ h _ Hvm Hh0 Hh8) as (bs & Hbs & Hle). rewrite Z_to_bv_bv_unsigned in Hle.
assert (R : getr (ms_regs ms) rs = Z_to_bv 64 h) by (rewrite (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS); exact Hrs).
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_ld tfibsegs _ _ _ _ _ rd rs (0%bv : bv 12) bs (ew E k) Hfetch Hec Hdec); [|exact Hle].
rewrite R. replace (v_addi (Z_to_bv 64 h) (bv_signed (0%bv : bv 12))) with (Z_to_bv 64 h : word); [exact Hbs|].
apply bv_eq. unfold v_addi. rewrite !Z_to_bv_unsigned. change (bv_signed (0%bv : bv 12)) with 0.
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, Z.mod_mod by lia. reflexivity.
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, SOff k 0)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). cbn [sv_denot].
rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.
(* A one-byte zero-extending load (lbu rd, imm(rs)) of the byte at h, whose value v is named by the symbolic value t:
   an atom (SOff k 0) for a byte the walk does not know, or a literal (SLit v) for a byte it knows. *)
Lemma cs_lbu : forall (W : world tfibsegs) E ss ms md (rd rs : bv 5) (w : Z) (imm : bv 12) (h v : Z) (t : sv) (K : nat),
st_ok tfibsegs E ss (restrict (w_H W) ms) -> ss_resv ss = None -> ss_atoms_lt K ss = true ->
clookup tbl_cs (ss_pc ss) = Some w -> decode_any (Z_to_bv 32 w) = Some (Load SZ1 false rd rs imm, 4) ->
bv_eqb rd 0%bv = false ->
v_addi (sv_denot E (sr_get (ss_regs ss) rs)) (bv_signed imm) = Z_to_bv 64 h -> 0 <= h < 2 ^ 64 ->
aview tfibsegs (w_H W) (ms_mem ms) h = Some v -> sv_denot E t = Z_to_bv 64 v ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
st_ok tfibsegs E (set_regs_pc ss [(rd, t)] (ss_pc ss + 4)) (restrict (w_H W) ms1) /\
ms_mem ms1 = ms_mem ms).
Proof.
intros W E ss ms md rd rs w imm h v t K HS Hrv Hat Hlk Hdec Hrd Hrs Hh Hv Ht. pose proof YF0x.Hwx_tfa as Hwx.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) E _ _ HS Hrv) as Hshape.
pose proof (tbl_cs_ok _ _ Hlk) as Hfetch.
assert (Hec : is_ecall (Z_to_bv 32 w) = false).
{ unfold is_ecall. destruct (bv_eqb (Z_to_bv 32 w) _) eqn:Eq; [|reflexivity].
apply bv_eqb_eq in Eq. rewrite Eq in Hdec. vm_compute in Hdec. discriminate. }
unfold aview in Hv. destruct (mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) h) as [b|] eqn:Hb; [|discriminate].
cbn [option_map] in Hv. injection Hv as Hbv.
assert (R : getr (ms_regs ms) rs = sv_denot E (sr_get (ss_regs ss) rs)) by (apply (st_ok_restrict_reg tfibsegs (w_H W) E ss ms rs HS)).
assert (Hrdn : rdn tfibsegs (mrestrict (w_H W) (ms_mem ms)) (v_addi (getr (ms_regs ms) rs) (bv_signed imm)) 1%nat = Some [b]).
{ rewrite R, Hrs. apply (proj2 (rdn_mbytes tfibsegs _ 1 h [b])). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia.
rewrite Z.add_0_r. exact Hb. }
rewrite Hshape. eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
- rewrite restrict_mkst_fx. apply (step_lbu tfibsegs _ _ _ _ _ rd rs imm b Hfetch Hec Hdec Hrdn).
- intros model' Hsbm. rewrite (same_but_materialized_wvb md model' Hsbm). rewrite Hrd.
cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
apply SRr_ret. split; [reflexivity|]. eexists _, _. split; [reflexivity|]. split; [|reflexivity].
rewrite restrict_mkst_fx. rewrite Hshape in HS. rewrite restrict_mkst_fx in HS.
replace (v_addi (Z_to_bv 64 (ss_pc ss)) 4) with (Z_to_bv 64 (ss_pc ss + 4) : word)
by (apply bv_eq; unfold v_addi; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64);
rewrite Zplus_mod_idemp_l; reflexivity).
apply (st_ok_set_regs tfibsegs K E E ss _ _ _ (ss_pc ss + 4) _ [(rd, t)] HS (env_agree_refl K E) Hat Hrv).
+ cbn. rewrite ?Bool.orb_false_r. reflexivity.
+ intros r Hr. cbn in Hr. rewrite ?Bool.orb_false_r in Hr. rewrite getr_other; [reflexivity|].
intros ->. rewrite bv_eqb_refl in Hr. discriminate.
+ constructor; [|constructor]. cbn [fst snd]. split; [exact Hrd|].
rewrite getr_same by (intros H'; rewrite H', bv_eqb_refl in Hrd; discriminate). rewrite Ht.
apply bv_eq. rewrite !Z_to_bv_unsigned. subst v. pose proof (u8_range b).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.
End f.

(* ---- the interfaces of the pieces (each proved in its own file) ---- *)
Section iface. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* lib/AU/FMstrcspn_musl.v: the loops of musl __strchrnul for a byte c <> 0, from 0x9186c (a0 = the string, a1 = c)
   to the epilogue 0x91928: a0 = the address of the first byte that is c or NUL. No store; a0 and a2 .. a7 change. *)
Definition CS_MUSL_LOOPS : Prop :=
forall (s : list byte) (c : byte) (p : word) (mem rom : word -> option byte) regs,
~ In NUL s -> bv_unsigned c <> 0 ->
bv_unsigned p + Z.of_nat (length s) + 8 < 2 ^ 64 ->
(forall j, (j <= length s)%nat -> rdn tfibsegs mem (Z_to_bv 64 (bv_unsigned p + Z.of_nat j)) 1 = Some [nth j (s ++ [NUL]) NUL]) ->
(forall a : Z, bv_unsigned p + Z.of_nat (length s) < a
< bv_unsigned p + Z.of_nat (length s) - (bv_unsigned p + Z.of_nat (length s)) mod 8 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 <> None) ->
(forall a : Z, YE3a.tfib_D_const_HIGHS_0x8080808080808080 <= a < YE3a.tfib_D_const_ONES_0x0101010101010100 + 8 ->
rdn tfibsegs mem (Z_to_bv 64 a) 1 = rdn tfibsegs (fun _ : word => @None byte) (Z_to_bv 64 a) 1) ->
getr regs 10 = p -> getr regs 11 = Z_to_bv 64 (bv_unsigned c) ->
exists regs', msteps tfibsegs (mkst regs (Z_to_bv 64 CS_LOOP) mem rom) (mkst regs' (Z_to_bv 64 CS_LOOP_END) mem rom)
/\ getr regs' 10 = Z_to_bv 64 (bv_unsigned p + Z.of_nat (PPgWrap.cspn_len [c] s))
/\ (forall r : bv 5, r <> 10%bv -> r <> 12%bv -> r <> 13%bv -> r <> 14%bv -> r <> 15%bv -> r <> 16%bv -> r <> 17%bv ->
getr regs' r = getr regs r).
Variable B : asyms.
(* lib/AU/FMstrcspn_chk1.v: the range check of the set, 0x42d38 .. 0x42d88, for a range of n <= 2 bytes at p
   (s3 = p, a0 = n - 1). On these paths it calls nothing and stores nothing; it writes s2 (= n) and sets
   a0 = s5. *)
Definition CS_CHK1 : Prop :=
forall ly S (W : world tfibsegs) regs mem md p n,
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + CHK_SCR <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - CHK_SCR <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 (n - 1) -> getr regs 19 = w64 p ->
0 < p -> 1 <= n <= 2 -> p + n <= 2 ^ 63 ->
amem_range p n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
SRr tfibsegs W (cfg_at tfibsegs CS1_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs CS1_END regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 18 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
getr regs' 10 = getr regs 21 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHK_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* lib/AU/FMstrcspn_chk2.v: the range check of the string, 0x42d88 .. 0x42de0, for a range of n bytes at p
   (s1 = p, a0 = s5 = n - 1, s7 = the flags object). For n > 64 it calls __asan_region_is_poisoned 0x5437c
   (64-byte frame, and 8 more bytes below it for the mem_is_zero stretch). It writes s1, s2 and s3 and leaves
   a0 = n - 1. *)
Definition CS_CHK2 : Prop :=
forall ly S (W : world tfibsegs) regs mem md p n,
AR tfibsegs B ly S W mem md ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + CHK_SCR <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - CHK_SCR <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 (n - 1) -> getr regs 21 = w64 (n - 1) -> getr regs 9 = w64 p -> getr regs 23 = w64 CS_FLAGS ->
0 < p -> 1 <= n < 2 ^ 32 -> p + n <= 2 ^ 63 ->
amem_range p n ->
range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF p n ->
shadow_hull_vis (aview tfibsegs (w_H W) mem) p n ->
SRr tfibsegs W (cfg_at tfibsegs CS2_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs CS2_END regs' mem' md' /\
AR tfibsegs B ly S W mem' md' /\
(forall r, acallee_saved r -> r <> 9 -> r <> 18 -> r <> 19 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) /\
same_but_materialized md md' /\
getr regs' 10 = w64 (n - 1) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CHK_SCR <= a < spZ regs) -> aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a)).
(* The state at 0x42d38 that lib/AU/FMstrcspn_front.v reaches from the trampoline and lib/AU/FMstrcspn.v continues
   from: regs, mem, md are the wrapper's entry state (x = a0, y = a1), r the result of musl strcspn. The ten
   words the prologue saved (ra, s0 .. s8) are below the entry sp; nothing outside [sp - CS_WIN, sp) changed. *)
Definition CS_SAVED : list (Z * Z) :=
[(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56); (22, -64); (23, -72); (24, -80)].
Definition CS_KEPT : list Z := [3; 4; 20; 24; 25; 26; 27].
Definition cs_mid (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (x y r : Z) (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model) : Prop :=
AR tfibsegs B ly S W mem1 md1 /\ same_but_materialized md md1 /\
getr regs1 2 = w64 (spZ regs - CS_FRAME) /\ getr regs1 8 = w64 (spZ regs) /\
getr regs1 9 = w64 x /\ getr regs1 19 = w64 y /\ getr regs1 10 = w64 1 /\
getr regs1 21 = w64 r /\ getr regs1 23 = w64 CS_FLAGS /\
(forall q, In q CS_KEPT -> getr regs1 (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q)) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - CS_WIN <= a < spZ regs) -> aview tfibsegs (w_H W) mem1 a = aview tfibsegs (w_H W) mem a) /\
(forall a, apresent (w_H W) mem a -> apresent (w_H W) mem1 a) /\
(forall rz off, In (rz, off) CS_SAVED ->
val_mem tfibsegs (mrestrict (w_H W) mem1) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
End iface.
