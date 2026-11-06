(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: made for libreac/fuzz_knock's ASan harness walk of LLVMFuzzerTestOneInput
   (fuzz_knock.asan, sha256 61768cf4739b7641c99c825dde45eddafc55b601d41109555be0272fc7ca4118): SEGMENT S3 LOOP,
   pc 0x7f10c-0x7f190, from the loop head ss_L (INV_L (S fuel)) to ss_T (INV_T fuel) at 0x7f194.
   Donor model: proofs/cgif/cgif_file_fuzzer/lib/A/ACf1.v at c8557374ad2e --- rt_B_aux :410-497 (the header
   bytes: one in_bytes :396-407, add_atom_win, in_region and rd_run per group of bytes, a br_go between groups) and
   pin_reg :268-280 (a register pinned to a fresh atom). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_knock/lib/A/APgMain3.v, with its module paths and module names changed; 649 of its 708 lines of code are new or changed and 136 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgMain3.v of this library, for reac-pw/fuzz_pin's
   image B (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). What
   differs: the imports are image B's lib/AU twins (the core's Y files, lib/AU/PPgSat.v, PPgMainCall.v, PPgMainRt.v,
   PPgMainSt.v; the shared texts lib/A/PPgBase.v and PPgCSpec.v are the same); fuzz_catalogue_row is taken at image
   B's entry 0x80fb4 and the table at image B's PM_CAT 0x98000 (rows 0x98000 .. 0x98b90); the code is image B's,
   with its register allocation (the byte read in s6, the flags byte in s10, s9 = SB; image A: s10, s9, s6) and the
   compiler's added checks of image B, each a branch to the trap word 0x80ab8 ("the trap branches"), walked and
   shown not taken: 0x80894 (`bltu s11,s5`, q + i wraps: split, refuted by ~q = 2 ^ 64 - 1 - q > i), 0x80a64 (`bgeu
   s5,s11`, q + tok >= 2 ^ 64 - 1: split, refuted by tok < ~q), 0x80a8c / 0x80a90 (`bne a0,-1`, q + tok = 2 ^ 64 - 1
   goes to the trap: decided by the executor from the range [4096, 2 ^ 47 - 2 ^ 23] of slot 663 = q + tok) and
   0x80a98 (`bnez` of want & 7: decided by the executor, which computes want & 7 = 0 from the alignment 8 of slot
   104 = want = row_addr cat i, cat mod 8 = 0); the cuts are image B's (ss_S3L at 0x80894, ss_S3E at 0x808e0) and the
   two invariants carry slot 106 (~q) from ss_C.

   S3 of the walk of reac-pw/fuzz_pin's LLVMFuzzerTestOneInput at image B (0x806b4): from ss_C (0x8088c) to ss_D
   (0x808f0), the cut states of lib/AU/PPgMainSt.v. rule 24 (reuse): no function is proved here; this is one segment
   of the walk.

   THE CODE (the neutral disassembly of image B's function; s3 = q, a0 = len, s10 = the flags, s11 = ~q):
     0x8088c s5 := 0; 0x80890 a2 := ':' (0x3a)
     0x80894 bltu s11,s5 -> 0x80ab8 (the trap branch, not taken); 0x80898 a1 := q + i; 0x8089c-0x808a8 the
       instrumented check of q + i (slow path 0x808c0, error path 0x808cc not reached: the byte is in the block
       (q, k + 1)); 0x808ac s6 := q[i]; 0x808b0 s6 = ':' -> 0x808e0; 0x808b4 i := i + 1; 0x808b8 i <> len ->
       0x80894; 0x808bc -> 0x808dc s5 := len
     0x808e0 a0 := flags & 7; 0x808e4 a0 = 0 -> 0x80a48; else 0x808e8 s4 := 0, s5 := 0 -> 0x808f0
     0x80a48 a0 := q, a1 := tok; 0x80a50 fuzz_catalogue_row (0x80fb4, ra 0x80a54) through its contract
       tpin_row_specX: a0 = row_ptr PM_CAT (firstn tok s); 0x80a54 a0 = 0 -> 0x808e8
     0x80a58 s4 := a0 (want); 0x80a60 s6 <> ':' -> 0x80a94; 0x80a64 bgeu s5,s11 -> 0x80ab8 (the trap branch, not
       taken); 0x80a68 a0 := q + tok; 0x80a6c s5 := q + tok + 1, the check of it (slow path 0x80ae4, error path 0x80af0
       not reached), 0x80a80 a1 := q[tok + 1]; a1 = 0 -> 0x80a94; 0x80a8c a0 <> -1 -> 0x808f0, else 0x80a90 -> 0x80ab8
       (the trap, not reached)
     0x80a94 a0 := want & 7; 0x80a98 a0 <> 0 -> 0x80ab8 (the trap branch, not taken); 0x80a9c the check of want + 8
       (error path 0x80af4 not reached: the table's shadow is 0, F-CAT); 0x80ab0 s5 := the 8 bytes at want + 8 =
       PM_DP i (F-CAT); -> 0x808f0
   THE CUTS INSIDE THIS FILE: ss_S3L, the loop head 0x80894 (i in slot 635; a1 a3 a4 s6 dead in window 631), and
   ss_S3E, the loop exit 0x808e0 (tok in slot 640, the last byte read in slot 641; a1 a3 a4 dead in window 642).
   The loop is an induction on fuel >= len - i (pm_S3_loop). The back edge renames i + 1 into slot 635 through slot
   630. Per-pass atoms: 636 (q + i), 637 (q[i]); after the call 104 (want), 105 (want_label), 663 (q + tok), 661
   (q + tok + 1), 662 (q[tok + 1]). Every slot is in 630..699 or a cut slot of ss_D.
   The tactics obl_q (the moving-cursor obligation) and pm3_region_kept_eq follow fuzz_knock's lib/A/APgLoop0.v
   obl_cur and lib/A/APgMain2.v rt_region_kept_eq (origin/ossv/recipes 6ebe35ba632); the call follows APgMain2.v's
   journal-threaded call (SRr_bind, reseatL); pin_row_site gives the callee's premises. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YI16 YM05 YCeo.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgSat PPgMainCall PPgMainRt PPgMainSt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------ the byte list and the ':' scan ------------------------------ *)
Lemma pm3_zb_app : forall s : list byte, pin_zbytes s ++ [0] = pin_zbytes (s ++ [NUL]).
Proof. intros s. unfold pin_zbytes. rewrite map_app. reflexivity. Qed.
Lemma pm3_zb_nth : forall (s : list byte) j, nth j (pin_zbytes s ++ [0]) 0 = bv_unsigned (nth j (s ++ [NUL]) NUL).
Proof. intros s j. rewrite pm3_zb_app. unfold pin_zbytes. exact (map_nth (fun b : byte => bv_unsigned b) (s ++ [NUL]) NUL j). Qed.
Lemma pm3_zb_len : forall s : list byte, length (pin_zbytes s ++ [0]) = S (length s).
Proof. intros s. unfold pin_zbytes. rewrite length_app, length_map. cbn [length]. lia. Qed.
Lemma pm3_colon_step : forall (s : list byte) i, (i <= colon_idx s)%nat -> (i < length s)%nat ->
(bv_unsigned (nth i s NUL) = COLON /\ colon_idx s = i) \/ (bv_unsigned (nth i s NUL) <> COLON /\ (S i <= colon_idx s)%nat).
Proof.
induction s as [|x s IH]; intros i Hi Hl; cbn [length] in Hl; [lia|].
cbn [colon_idx] in Hi |- *. destruct (bv_unsigned x =? COLON) eqn:E.
- assert (i = 0)%nat as -> by lia. cbn [nth]. left. split; [apply Z.eqb_eq; exact E | reflexivity].
- destruct i as [|i]; cbn [nth].
  + right. split; [apply Z.eqb_neq; exact E | lia].
  + destruct (IH i ltac:(lia) ltac:(lia)) as [[H1 H2] | [H1 H2]]; [left | right]; (split; [exact H1 | lia]).
Qed.
Lemma pm3_garr8_frame : forall E rs (H : word -> bool) m m' q (l : list Z),
frame_of E rs (mrestrict H m) (mrestrict H m') ->
(forall j, (j < length l)%nat -> ~ in_wrange E rs (q + Z.of_nat j)) -> 0 <= q -> q + Z.of_nat (length l) <= 2 ^ 64 ->
garr8 tfibsegs (mrestrict H m) q l -> garr8 tfibsegs (mrestrict H m') q l.
Proof.
intros E rs H m m' q l HFr Hno Hq Hql HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
intros k Hk. assert (k = 0%nat) as -> by lia. specialize (V 0%nat ltac:(lia)). unfold mbyte in *.
rewrite HFr; [exact V|]. rewrite unsigned_lit_small by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. apply Hno. exact Hj.
Qed.
Section kp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the n bytes at q survive a call that keeps every byte the contract's post names *)
Lemma pm3_garr8_kept : forall (H H' : word -> bool) (m m' : word -> option byte) q (l : list Z),
(forall j, (j < length l)%nat -> aview tfibsegs H' m' (q + Z.of_nat j) = aview tfibsegs H m (q + Z.of_nat j)) ->
garr8 tfibsegs (mrestrict H m) q l -> garr8 tfibsegs (mrestrict H' m') q l.
Proof.
intros H H' m m' q l Hk HG j Hj. destruct (HG j Hj) as [V R]. split; [|exact R].
eapply val_mem_kept; [|exact V]. intros k Hk'. assert (k = 0) as -> by (cbn in Hk'; lia). rewrite Z.add_0_r. exact (Hk j Hj).
Qed.
(* [knock lib/A/APgMain2.v rt_region_kept_eq] *)
Lemma pm3_region_kept_eq : forall E (H H2 : word -> bool) (m m2 : word -> option byte) n b lo hi wlo whi cs,
bv_unsigned (ew E n) = b ->
(forall a, b + lo <= a < b + hi -> aview tfibsegs H2 m2 a = aview tfibsegs H m a) ->
(forall a, b + wlo <= a < b + whi -> apresent H2 m2 a) ->
region_kept tfibsegs E (mrestrict H m) (mrestrict H2 m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H H2 m m2 n b lo hi wlo whi cs Hn Hav Hp.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Hn; intros a Ha.
- apply (mbyte_of_aview tfibsegs). apply Hav. exact Ha.
- intros _. apply (apresent_writable tfibsegs). apply Hp. exact Ha.
Qed.
End kp.

(* ------------------------------ the two internal cut states ------------------------------ *)
(* the loop head 0x80894: ss_C with a2 = ':' (0x3a), s5 = i (slot 635); a1 a3 a4 s6 dead (window 631) *)
Definition ss_S3L : sstate := Eval vm_compute in
ss_havoc_regs (ss_set_pc (ss_set_regs ss_C [(12%nat, SLit 58); (21%nat, SOff 635 0)]) 0x80894) 631 [11; 13; 14; 22]%nat.
(* the loop exit 0x808e0: s5 = tok (slot 640), s6 = the last byte read (slot 641); a1 a3 a4 dead (window 642) *)
Definition ss_S3E : sstate := Eval vm_compute in
ss_havoc_regs (ss_set_pc (ss_set_regs ss_C [(12%nat, SLit 58); (21%nat, SOff 640 0); (22%nat, SOff 641 0)]) 0x808e0) 642 [11; 13; 14]%nat.
Definition pm3_L_deads_bv : list (bv 5) := [11; 13; 14; 22]%bv.
Definition pm3_E_deads_bv : list (bv 5) := [11; 13; 14]%bv.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Definition INV_S3L (B : asyms) (MT : ameter_ops) (fuel : nat) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k = 1 /\ acc <= mo_malloc MT (2 ^ 26) /\
exists q kk fl (i : nat),
ew E 100 = Z_to_bv 64 q /\ ew E 102 = Z_to_bv 64 kk /\ ew E 103 = Z_to_bv 64 fl /\ ew E 106 = Z_to_bv 64 (2 ^ 64 - 1 - q) /\
ew E 635 = Z_to_bv 64 (Z.of_nat i) /\
kk = Z.of_nat (pin_k (c_pl cx)) /\ 0 < kk /\ fl = pin_flags (c_pl cx) /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(q, kk + 1)] /\
garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) q (pin_zbytes (pm_s cx) ++ [0]) /\
(i <= colon_idx (pm_s cx))%nat /\ (i < length (pm_s cx))%nat /\ (length (pm_s cx) - i <= fuel)%nat.
Definition INV_S3E (B : asyms) (MT : ameter_ops) : rtcx -> env -> Z -> Z -> alayout -> astate -> world tfibsegs -> machine_state -> Model -> Prop :=
fun cx E k acc ly3 S3 W3 ms3 md3 => k = 1 /\ acc <= mo_malloc MT (2 ^ 26) /\
exists q kk fl c,
ew E 100 = Z_to_bv 64 q /\ ew E 102 = Z_to_bv 64 kk /\ ew E 103 = Z_to_bv 64 fl /\ ew E 106 = Z_to_bv 64 (2 ^ 64 - 1 - q) /\
ew E 640 = Z_to_bv 64 (Z.of_nat (colon_idx (pm_s cx))) /\ ew E 641 = Z_to_bv 64 c /\
kk = Z.of_nat (pin_k (c_pl cx)) /\ 0 < kk /\ fl = pin_flags (c_pl cx) /\
ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(q, kk + 1)] /\
garr8 tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) q (pin_zbytes (pm_s cx) ++ [0]) /\
0 <= c < 256 /\ (c = COLON <-> (colon_idx (pm_s cx) < length (pm_s cx))%nat).
End b.

(* ------------------------------ local walk tactics ------------------------------ *)
Ltac pl_run HS HJ AG fpos F EFA :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac pl_run_to HS HJ AG fpos F EFA stop :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Ltac br_split HS Hc :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ => srr_branch_tok tfibtbl_lib_ok HS SH RTBspan end;
lazymatch goal with Hb : branch_taken _ _ _ = _ |- _ => rename Hb into Hc end.
Ltac pin_by HS r e dtac :=
lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
let eo := eval vm_compute in (sr_get (ss_regs ssx) r) in
let Hv := fresh "Hv" in
assert (Hv : sv_denot Ev e = sv_denot Ev eo) by dtac;
let HS3 := fresh "HS3" in
pose proof (st_ok_pin_rege Ev ssx msx r e HS ltac:(intros X; discriminate X)
(eq_trans Hv (eq_sym (st_ok_reg tfibsegs Ev ssx msx r HS)))) as HS3;
clear HS Hv; rename HS3 into HS; norm_ss HS end.
(* the block (q, kk + 1) malloc returned, before the call: In, req_size, the block law, off the image and off F *)
Ltac blk_facts B ly3 S3 q kk Eab3 HJ3 Hfin3 EFA3 F :=
let L := rnLAWS in
assert (Hq3 : In (q, kk + 1) (ablocks B ly3 S3)) by (rewrite Eab3; apply in_or_app; right; left; reflexivity);
assert (Hrq : req_size (kk + 1) = kk + 1) by (unfold req_size; destruct (Z.eqb_spec (kk + 1) 0); lia);
destruct (al_blocks _ _ L _ _ _ _ _ q (kk + 1) (proj1 HJ3) Hq3) as (Hq16 & Hq4096 & Hqceil & HqApp & _);
rewrite Hrq in Hqceil, HqApp;
pose proof (blk_off_img B _ _ _ _ _ q (kk + 1) (proj1 HJ3) Hq3) as HqImg; rewrite Hrq in HqImg;
pose proof (sep_block_frame tfibsegs B L ly3 S3 _ _ _ q (kk + 1) 1 _ (proj1 HJ3) Hq3 Hfin3) as HqF;
unfold zdisjoint in HqF; cbn [fst snd] in HqF; change (fs_frame_bytes 1) with 128 in HqF; rewrite EFA3 in HqF; fold F in HqF;
rewrite Hrq in HqF.
(* the n bytes at q survive a run: no region the run writes covers them *)
Ltac gkeep HGq AG :=
lazymatch goal with HFr : frame_of ?Ef ?rs (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m1) |- _ =>
lazymatch type of HGq with garr8 _ (mrestrict Hh m0) ?q ?l =>
let HG2 := fresh "HGk" in
assert (HG2 : garr8 tfibsegs (mrestrict Hh m1) q l);
[ apply (pm3_garr8_frame Ef rs Hh m0 m1 q l HFr);
  [ let j := fresh "j" in let Hj := fresh "Hj" in let rg := fresh "rg" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
    intros j Hj (rg & Hin & Hrg); rewrite pm3_zb_len in Hj;
    lazymatch type of Hin with In _ ?rs0 => let rs1 := eval vm_compute in rs0 in change (In rg rs1) in Hin end; cbn [In] in Hin;
    repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg; revert Hrg; evalE AG; intros Hrg; lia|]);
    destruct Hin
  | lia | rewrite pm3_zb_len; lia | exact HGq ]
| clear HGq; rename HG2 into HGq ] end end.

(* a read-only region with one byte chunk over the byte at the atom E's slot, from its val_mem *)
Ltac in_region_v HS R Ex Vb Rb Eb AG keep :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv R HS eq_refl) as HS3;
specialize (HS3 ltac:(
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
ewpeel; rewrite Ex, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
apply Forall_cons; [ eapply rt_chunk1_of_val; [ rewrite Z.add_0_r; exact Vb | exact Rb | ewpeel; exact Eb ] | apply Forall_nil ]));
specialize (HS3 ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; first [keep; zones; req_lits; lia | zone_lia]));
clear HS; rename HS3 into HS; norm_ss HS end.
(* the shadow-check obligation of a byte of the block (q, kk + 1), at an atom of the address [APgLoop0.v obl_cur] *)
Ltac obl_q HJx HEx HEbx Hin Hrq :=
let L := rnLAWS in
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEx with _ = Z_to_bv 64 ?cv =>
lazymatch type of Hin with In (?pb, ?sz) _ =>
first [ rewrite (U_atom_off Ex n cv c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact HEx | ewpeel; exact HEx] | lia | lia]
| rewrite (U_atom Ex n cv); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact HEx | ewpeel; exact HEx] | lia] ];
eapply (obl_of_block tfibsegs _ L _ _ _ _ _ Ex (SOff bx 0) _ len pb sz (proj1 HJx) Hin);
[ rewrite (U_atom Ex bx SB); [reflexivity | cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact HEbx | ewpeel; exact HEbx] | unfold SB; lia]
| lia | rewrite Hrq; lia ] end end end.
Ltac rd_run_q HS HJ AG fpos F EFA HEx HEbx Hin Hrq :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_tok tfibtbl_lib_ok HS HJ SH RTBspan;
try (lazymatch goal with |- range_addressable _ _ _ _ => obl_q HJ HEx HEbx Hin Hrq end);
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
(* drop the branch conditions of the state (they name atoms a rename is about to reuse) *)
Ltac drop_conds HS :=
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
let fa := eval vm_compute in (f_atoms (ss_facts ssx)) in
let al := eval vm_compute in (f_alias (ss_facts ssx)) in
let HS3 := fresh "HS3" in
pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa [] al HS ltac:(incl_lit_tac) ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; destruct Hx) ltac:(incl_lit_tac)) as HS3;
clear HS; rename HS3 into HS; norm_ss HS end.
Lemma pm3_denot_add_off : forall E a b x y c, ew E a = Z_to_bv 64 x -> ew E b = Z_to_bv 64 y -> 0 <= x -> 0 <= y ->
0 <= x + c -> x + c + y < 2 ^ 64 -> x < 2 ^ 64 -> sv_denot E (SAlu ALU_ADD (SOff a c) (SOff b 0)) = Z_to_bv 64 (x + c + y).
Proof.
intros E a b x y c Ha Hb Hx Hy Hxc Hxy Hx64. rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom_off E a x c Ha), (U_atom E b y Hb) by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma pm3_ra_sub : forall (rd : Z -> option Z) Bs a len a' len', range_addressable rd Bs a len -> a <= a' -> a' + len' <= a + len ->
range_addressable rd Bs a' len'.
Proof. intros rd Bs a len a' len' H H1 H2 x Hx. apply H. lia. Qed.
(* the table row's display pointer at want + 8: a read-only region at slot 104 (want), its word at slot 105 *)
Ltac tab_region HS AG E104 E105 Vdp Rdp :=
lazymatch type of HS with st_ok _ ?Ev ?ssv ?msv =>
let HS3 := fresh "HS3" in
pose proof (ast_ok_add_region tfibsegs Ev ssv msv (YP09.mkRegion (Some 104%nat) 8 16 0 0 [YP09.mkChunk 8 (CVal 8 (SOff 105 0))]) HS eq_refl) as HS3;
specialize (HS3 ltac:(
unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict];
ewpeel; rewrite E104, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split; [intros oo Hoo; lia|];
apply Forall_cons; [ eapply (chunk_ok_val tfibsegs Ev _ _ 8 8 (SOff 105 0) _); [ rewrite sv_denot_SOff0; ewpeel; exact E105 | zside | zside | exact Vdp ] | apply Forall_nil ]));
specialize (HS3 ltac:(
lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
evalE AG; unfold A_GOT_shadow, A_shadow_glob, A_GOT_uar, A_uar_glob;
repeat split; zone_lia));
clear HS; rename HS3 into HS; norm_ss HS end.
(* the shadow-check obligation of the 8 bytes at want + 8, from the table's range_addressable *)
Ltac obl_tab HEw HEbx RAc :=
lazymatch goal with |- range_addressable _ (U ?Ex (SOff ?bx 0)) (U _ (SOff ?n ?c)) ?len =>
lazymatch type of HEw with _ = Z_to_bv 64 ?cv =>
rewrite (U_atom_off Ex n cv c); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact HEw | ewpeel; exact HEw] | lia | lia];
rewrite (U_atom Ex bx SB); [| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; first [exact HEbx | ewpeel; exact HEbx] | unfold SB; lia];
rewrite SB_SHADOW_OFF;
eapply pm3_ra_sub; [exact RAc | unfold CAT_BYTES; lia | unfold CAT_BYTES; lia] end end.
Ltac rd_run_tab_to HS HJ AG fpos F EFA HEw HEbx RAc stop :=
reshok HS;
lazymatch goal with SH : sh_ok _ _ _ _ _ |- _ =>
aj_run_to_tok tfibtbl_lib_ok HS HJ SH RTBspan stop;
try (lazymatch goal with |- range_addressable _ _ _ _ => obl_tab HEw HEbx RAc end);
try (lazymatch goal with |- awr_ok _ _ _ _ _ _ _ _ _ => awrRT AG fpos F EFA end) end.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {ROB : YCeh.ro_tfa_below_ofl}.
Section d.
Variable B : asyms. Variable MT : ameter_ops. Hypothesis MTL : ameter_laws MT.
Variable FP : list (Z * Z). Variable POST : rtcx -> world tfibsegs -> config -> Prop. Hypothesis FP0 : FP = [].
Hypothesis TL : TfibLib B. Hypothesis LAWS : AR_laws tfibsegs B. Hypothesis ML : model_laws (as_universe B).
Let HBcode := tl_code B TL. Let HBgot := tl_got_shadow B TL. Let HBcell := tl_shadow_cell B TL.
Let HBguar := tl_got_uar B TL. Let HBuar := tl_uar_cell B TL. Let errno_low := tl_env B TL.

Lemma pm_S3_entry : (forall fuel, rt_from B MT FP POST ss_S3L (INV_S3L B MT fuel)) -> rt_from B MT FP POST ss_C (INV_C B MT).
Proof.
intros RL. rt_prelude.
destruct HINV as (Hk & Hacc & q & kk & fl & E100 & E102 & E103 & E106 & Hkk & Hkk0 & Hfl & Eab3 & HGq).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
set (s := pm_s (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) in *.
assert (Hls : Z.of_nat (length s) = kk) by (unfold s, pm_s; cbn [c_pl]; rewrite pin_str_length; lia).
blk_facts B ly3 S3 q kk Eab3 HJ3 Hfin3 EFA3 F.
(* 0x8088c mv s5,zero; 0x80890 li a2,0x3a; stop at the loop head 0x80894 *)
pl_run_to HS HJ3 AG fpos F EFA3 0x80894.
gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
add_atom_win HS 635%nat (Z_to_bv 64 0) E635.
pin_by HS (21%bv : bv 5) (SOff 635 0) ltac:(rewrite sv_denot_SOff0, E635; reflexivity).
ra_join_win HS ss_S3L 631%nat pm3_L_deads_bv ltac:(idtac).
rb HS AG E10 E11 E32 E10n E11n E32n.
rt_hand (RL (length s)) HS. fold s.
split; [exact Hk|]. split; [exact Hacc|].
exists q, kk, fl, 0%nat.
repeat match goal with |- _ /\ _ => split end; first [eassumption | lia].
Qed.

Lemma pm_S3_body : forall f, rt_from B MT FP POST ss_S3E (INV_S3E B MT) -> rt_from B MT FP POST ss_S3L (INV_S3L B MT f) ->
rt_from B MT FP POST ss_S3L (INV_S3L B MT (S f)).
Proof.
intros f RE RL. rt_prelude.
destruct HINV as (Hk & Hacc & q & kk & fl & i & E100 & E102 & E103 & E106 & E635 & Hkk & Hkk0 & Hfl & Eab3 & HGq & Hic & Hil & Hif).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
set (s := pm_s (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) in *.
assert (Hls : Z.of_nat (length s) = kk) by (unfold s, pm_s; cbn [c_pl]; rewrite pin_str_length; lia).
blk_facts B ly3 S3 q kk Eab3 HJ3 Hfin3 EFA3 F.
(* 0x80894 bltu s11,s5: the trap branch; ~q = 2 ^ 64 - 1 - q (q + k + 1 <= the ceiling) is not below i < k *)
br_split HS Ht0.
all: hc_bool Ht0 ltac:(fun H => hc_atom H 106%nat (2 ^ 64 - 1 - q) E106 ltac:(clear - Hq4096 Hqceil Hkk0 C1; lia);
  hc_atom H 635%nat (Z.of_nat i) E635 ltac:(clear - Hil Hls Hq4096 Hqceil Hkk0 C1; lia)); hc_prop Ht0.
1: exfalso; clear - Ht0 Hil Hls Hq4096 Hqceil Hkk0 C1; lia.
clear Ht0. norm_ss HS.
(* 0x80898 add a1,s3,s5: a1 = q + i, pinned to slot 636 *)
pl_run_to HS HJ3 AG fpos F EFA3 0x8089c.
gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
destruct (HGq i ltac:(rewrite pm3_zb_len; lia)) as (Vb & Rb).
set (b := nth i (pin_zbytes s ++ [0]) 0) in Vb, Rb.
add_atom_win HS 636%nat (Z_to_bv 64 (q + Z.of_nat i)) E636.
pin_by HS (11%bv : bv 5) (SOff 636 0) ltac:(rewrite sv_denot_SOff0, E636; symmetry;
  apply (denot_add2 _ 100 635 q (Z.of_nat i)); first [ewpeel; eassumption | lia]).
add_fact HS 636%nat 4096 140737479966720 E636 ltac:(lia).
add_atom_win HS 637%nat (Z_to_bv 64 b) E637.
add_fact HS 637%nat 0 255 E637 ltac:(lia).
in_region_v HS (YP09.mkRegion (Some 636%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 637 0))]) E636 Vb Rb E637 AG idtac.
(* 0x8089c-0x808ac: the check of q + i (slow path 0x808c0, error 0x808cc not reached), lbu s6,0(a1); stop at beq s6,a2 *)
rd_run_q HS HJ3 AG fpos F EFA3 E636 E32n Hq3 Hrq.
gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
assert (Hbv : b = bv_unsigned (nth i s NUL)) by (unfold b; rewrite pm3_zb_nth, nth_app_nul by lia; reflexivity).
br_split HS Hc1.
all: hc_bool Hc1 ltac:(fun H => hc_atom H 637%nat b E637 ltac:(lia)); hc_prop Hc1.
- (* s6 = ':': tok = i, to the exit 0x808e0 *)
  destruct (pm3_colon_step s i Hic ltac:(lia)) as [[_ Hci] | [Hnc _]]; [| exfalso; unfold COLON in Hnc; lia].
  pl_run_to HS HJ3 AG fpos F EFA3 0x808e0.
  gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  add_atom_win HS 640%nat (Z_to_bv 64 (Z.of_nat i)) E640.
  pin_by HS (21%bv : bv 5) (SOff 640 0) ltac:(rewrite !sv_denot_SOff0, E640; ewpeel; rewrite E635; reflexivity).
  add_atom_win HS 641%nat (Z_to_bv 64 b) E641.
  pin_by HS (22%bv : bv 5) (SOff 641 0) ltac:(rewrite !sv_denot_SOff0, E641; ewpeel; rewrite E637; reflexivity).
  ra_join_win HS ss_S3E 642%nat pm3_E_deads_bv ltac:(idtac).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RE HS. fold s.
  split; [exact Hk|]. split; [exact Hacc|].
  exists q, kk, fl, b. rewrite Hci.
  repeat match goal with |- _ /\ _ => split end; first [eassumption | lia | (unfold COLON; split; intros; lia)].
- (* s6 <> ':' *)
  destruct (pm3_colon_step s i Hic ltac:(lia)) as [[Hco _] | [_ Hci]]; [exfalso; unfold COLON in Hco; lia |].
  (* 0x808b4 addi s5,s5,1; stop at bne a0,s5 *)
  pl_run HS HJ3 AG fpos F EFA3.
  gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  br_split HS Hc2.
  all: hc_bool Hc2 ltac:(fun H => hc_atom H 102%nat kk E102 ltac:(lia);
    rewrite (U_atom_off _ 635 (Z.of_nat i) 1) in H by first [ewpeel; exact E635 | lia]); hc_prop Hc2.
  + (* i + 1 <> len: the back edge to 0x80894 *)
    pl_run_to HS HJ3 AG fpos F EFA3 0x80894.
    gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    (* i := i + 1 in slot 635: through slot 630, after the branch conditions on 635 are dropped *)
    add_atom_win HS 630%nat (Z_to_bv 64 (Z.of_nat i + 1)) E630.
    pin_by HS (21%bv : bv 5) (SOff 630 0) ltac:(rewrite sv_denot_SOff0, E630, (denot_lit_U _ (SOff 635 1)); f_equal;
      symmetry; apply U_atom_off; [ewpeel; exact E635 | lia | lia]).
    drop_conds HS. clear E635.
    add_atom_win HS 635%nat (Z_to_bv 64 (Z.of_nat i + 1)) E635.
    pin_by HS (21%bv : bv 5) (SOff 635 0) ltac:(rewrite !sv_denot_SOff0, E635; ewpeel; rewrite E630; reflexivity).
    ra_join_win HS ss_S3L 631%nat pm3_L_deads_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RL HS. fold s.
    split; [exact Hk|]. split; [exact Hacc|].
    exists q, kk, fl, (Datatypes.S i). replace (Z.of_nat (Datatypes.S i)) with (Z.of_nat i + 1) by lia.
    repeat match goal with |- _ /\ _ => split end; first [eassumption | lia].
  + (* i + 1 = len: 0x808bc j 0x808dc, mv s5,a0, to the exit 0x808e0; tok = len *)
    pl_run_to HS HJ3 AG fpos F EFA3 0x808e0.
    gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    assert (Hce : colon_idx s = length s) by (pose proof (colon_idx_le s); lia).
    add_atom_win HS 640%nat (Z_to_bv 64 kk) E640.
    pin_by HS (21%bv : bv 5) (SOff 640 0) ltac:(rewrite !sv_denot_SOff0, E640; ewpeel; rewrite E102; reflexivity).
    add_atom_win HS 641%nat (Z_to_bv 64 b) E641.
    pin_by HS (22%bv : bv 5) (SOff 641 0) ltac:(rewrite !sv_denot_SOff0, E641; ewpeel; rewrite E637; reflexivity).
    ra_join_win HS ss_S3E 642%nat pm3_E_deads_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RE HS. fold s.
    split; [exact Hk|]. split; [exact Hacc|].
    exists q, kk, fl, b. rewrite Hce. replace (Z.of_nat (length s)) with kk by lia.
    repeat match goal with |- _ /\ _ => split end; first [eassumption | lia | (unfold COLON; split; intros; lia)].
Qed.
(* the ':' scan, closed by induction on fuel >= len - i *)
Lemma pm_S3_loop : rt_from B MT FP POST ss_S3E (INV_S3E B MT) -> forall fuel, rt_from B MT FP POST ss_S3L (INV_S3L B MT fuel).
Proof.
intros RE fuel. induction fuel as [|f IH].
- intros cx E k acc ly3 S3 W3 ms3 md3 _ _ _ _ _ HINV _. exfalso.
  destruct HINV as (_ & _ & q & kk & fl & i & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hil & Hif). lia.
- exact (pm_S3_body f RE IH).
Qed.


Hypothesis FCAT : pin_ro_law tfibsegs B PM_RLO PM_RHI PM_CAT PM_TP PM_DP PM_COLONP.
Hypothesis TROW : tpin_row_specX (SK := SK) tfibsegs B MT PM_RLO PM_RHI 0x80fb4 PM_CAT PM_TP PM_DP.
(* the call site 0x80a50 of fuzz_catalogue_row(q, tok): the walk's state there gives every premise of
   tpin_row_specX at (sa, n, sb) = (q, tok, firstn tok s) *)
Lemma pin_row_site : forall (cx : rtcx) ly3 S3 W3 mem3 md3 (regsc : bvmap 5 word) (q : Z) (tok : nat),
rt_base B MT cx ->
ajournal tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(1, c_fpos cx)] ly3 S3 W3 mem3 md3 1 ->
In (q, Z.of_nat (length (pm_s cx)) + 1) (ablocks B ly3 S3) ->
garr8 tfibsegs (mrestrict (w_H W3) mem3) q (pin_zbytes (pm_s cx) ++ [0]) ->
(tok <= length (pm_s cx))%nat ->
getr regsc 1 = w64 RT_row_ra -> spZ regsc = c_sp1 cx ->
getr regsc 3 = getr (c_regs cx) 3 -> getr regsc 4 = getr (c_regs cx) 4 -> s0Z regsc = spZ (c_regs cx) ->
(forall a, spZ (c_regs cx) <= a < 2 ^ 64 -> aview tfibsegs (w_H W3) mem3 a = aview tfibsegs (w_H (c_W cx)) (c_mem cx) a) ->
rdword (aview tfibsegs (w_H W3) mem3) (spZ (c_regs cx) - 8) = Some (raZ (c_regs cx)) ->
rdword (aview tfibsegs (w_H W3) mem3) (spZ (c_regs cx) - 16) = Some (s0Z (c_regs cx)) ->
pin_pre_kit tfibsegs B LLVMF_STK (spZ (c_regs cx)) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(1, c_fpos cx)] ly3 S3 W3 mem3 md3 1 regsc (rt_ch cx) T_row_STK EV_row /\
Z.of_nat tok = Z.of_nat (length (firstn tok (pm_s cx))) /\ 0 <= Z.of_nat tok < 2 ^ 32 /\ 0 < q /\
q + Z.of_nat tok <= 2 ^ 63 /\
garr8 tfibsegs (mrestrict (w_H W3) mem3) q (pin_zbytes (firstn tok (pm_s cx))) /\
range_addressable (aview tfibsegs (w_H W3) mem3) SHADOW_OFF q (Z.of_nat tok) /\
(0 < Z.of_nat tok -> shadow_hull_vis (aview tfibsegs (w_H W3) mem3) q (Z.of_nat tok)) /\
amem_range q (Z.of_nat tok) /\
(forall x, q <= x < q + Z.of_nat tok -> ~ (spZ regsc - T_row_STK <= x < spZ regsc)) /\
pin_cat_ok tfibsegs (mrestrict (w_H W3) mem3) (aview tfibsegs (w_H W3) mem3) PM_CAT PM_TP PM_DP /\
pin_cat_off_stack PM_CAT PM_TP regsc T_row_STK /\
arodata_okP tfibsegs PM_RLO PM_RHI B (aview tfibsegs (w_H W3) mem3).
Proof.
intros cx ly3 S3 W3 mem3 md3 regsc q tok HB HJ Hin3 HG Htok Hra Hsp Hgp3 Htp3 Hs0 HUP Vra Vs0.
pose proof HB as (HPRE & Hra0 & _ & _ & _ & _ & _ & _ & Hev & _ & HROD & Esp1 & _).
pose proof HPRE as (_ & _ & Hra4 & Hgp & Htp & Hstk & _ & Hch & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FFS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HTR : T_row_STK = 8256) by (unfold T_row_STK; rewrite Hes; reflexivity).
pose proof HJ as (HAR3 & HLY3 & _ & _ & _ & _ & Hnev3 & _).
destruct (sp1_facts (spZ (c_regs cx) + -128) ltac:(lia) ltac:(rewrite <- Zplus_mod_idemp_l, Hal16; reflexivity)) as (Hsp1r & Hsp1al & Hsp1al16).
rewrite <- Esp1 in Hsp1r, Hsp1al, Hsp1al16.
rewrite FFS in Hslo.
set (len := Z.of_nat (length (pm_s cx))) in *.
assert (Hlen0 : 0 <= len) by (subst len; lia).
assert (Hrq : req_size (len + 1) = len + 1) by (unfold req_size; destruct (Z.eqb_spec (len + 1) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin3) as (_ & Hq4096 & Hqceil & _ & _ & _ & Hqmax).
rewrite Hrq in Hqceil.
assert (Htokl : Z.of_nat tok <= len) by (subst len; lia).
assert (Qtop64 : ly_top (c_ly cx) <= 2 ^ 64) by lia.
assert (Qal8 : spZ (c_regs cx) mod 8 = 0) by (pose proof (Z.div_mod (spZ (c_regs cx)) 16 ltac:(lia)) as D; rewrite Hal16, Z.add_0_r in D; rewrite D; replace (16 * (spZ (c_regs cx) / 16)) with ((2 * (spZ (c_regs cx) / 16)) * 8) by lia; apply Z_mod_mult).
assert (Hch1 : achain ly3 (aview tfibsegs (w_H W3) mem3) (c_sp1 cx) (spZ (c_regs cx)) (rt_ch cx)).
{ unfold rt_ch. apply (achain_ly_top (c_ly cx)); [destruct HLY3 as (_ & _ & _ & _ & _ & _ & _ & _ & LT & _); exact LT|].
  exact (rt_chain (c_ly cx) _ _ (c_regs cx) (c_sp1 cx) Hch Qtop64 HUP Vra Vs0 Hra4 ltac:(lia) Qal8 ltac:(lia)). }
assert (EraX : raZ regsc = RT_row_ra) by (unfold raZ; rewrite Hra; apply unsigned_lit_small; unfold RT_row_ra; lia).
assert (HRO3 : arodata_okP tfibsegs PM_RLO PM_RHI B (aview tfibsegs (w_H W3) mem3))
  by (apply pm_arodataP; exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ HROD)).
assert (HCAT : pin_cat_ok tfibsegs (mrestrict (w_H W3) mem3) (aview tfibsegs (w_H W3) mem3) PM_CAT PM_TP PM_DP)
  by (eapply proj1; eapply pin_ro_law_at; [exact FCAT | exact HJ | exact HRO3]).
split.
{ split; [exact HJ|]. split; [rewrite Hra; apply ret_ok_even; vm_compute; reflexivity|].
  split; [rewrite EraX; unfold RT_row_ra; lia|].
  split; [rewrite Hgp3; exact Hgp|]. split; [rewrite Htp3; exact Htp|].
  split; [rewrite Hsp, Hs0; exact Hch1|].
  split; [rewrite Hsp; exact Hsp1al16|]. split; [rewrite Hsp, HTR, FFS; lia|]. split; [rewrite Hsp; lia|].
  unfold EV_row, RT_EV in *. lia. }
split; [rewrite firstn_length_le by exact Htok; reflexivity|].
split; [unfold MALLOC_MAX in Hqmax; lia|]. split; [lia|]. split; [lia|].
split.
{ assert (E : pin_zbytes (pm_s cx) ++ [0] = pin_zbytes (firstn tok (pm_s cx)) ++ (pin_zbytes (skipn tok (pm_s cx)) ++ [0]))
    by (unfold pin_zbytes; rewrite app_assoc, <- map_app, firstn_skipn; reflexivity).
  rewrite E in HG. intros j Hj. destruct (HG j ltac:(rewrite length_app; lia)) as [Hv Hr].
  rewrite app_nth1 in Hv, Hr by exact Hj. split; [exact Hv | exact Hr]. }
split; [apply (range_addressable_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (len + 1)); [exact HAR3 | exact Hin3 | lia | rewrite Hrq; lia]|].
split; [intros Hn0; apply (shadow_hull_vis_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (len + 1)); [exact HAR3 | exact Hin3 | lia | rewrite Hrq; lia | exact Hn0]|].
split; [apply (amem_range_of_block tfibsegs B LAWS ly3 S3 W3 mem3 md3 q (len + 1)); [exact HAR3 | exact Hin3 | lia | rewrite Hrq; lia]|].
split; [intros x Hx; rewrite Hsp, HTR; lia|].
split; [exact HCAT|].
split; [apply pin_sat_cat_off_stack; rewrite ?HTR; [lia | rewrite Hsp; lia]|].
exact HRO3.
Qed.
Lemma pm_S3_post : rt_from B MT FP POST ss_D (INV_D B MT) -> rt_from B MT FP POST ss_S3E (INV_S3E B MT).
Proof.
intros RD. rt_prelude.
destruct HINV as (Hk & Hacc & q & kk & fl & c & E100 & E102 & E103 & E106 & E640 & E641 & Hkk & Hkk0 & Hfl & Eab3 & HGq & Hc0 & Hcc).
relowRT HS AG E10 E11 E32 E10n E11n E32n.
set (s := pm_s (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) in *.
assert (Hls : Z.of_nat (length s) = kk) by (unfold s, pm_s; cbn [c_pl]; rewrite pin_str_length; lia).
blk_facts B ly3 S3 q kk Eab3 HJ3 Hfin3 EFA3 F.
assert (Hfl8 : 0 <= fl < 256) by (rewrite Hfl; apply pin_flags_range).
pose proof (colon_idx_le s) as Htl.
(* 0x808e0 andi a0,s10,7; stop at beqz a0 *)
pl_run HS HJ3 AG fpos F EFA3.
gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
rb HS AG E10 E11 E32 E10n E11n E32n.
br_split HS Hc1.
all: hc_bool Hc1 ltac:(fun H => hc_atom H 103%nat fl E103 ltac:(lia)); hc_prop Hc1.
- (* flags & 7 = 0: 0x80a48 mv a0,s3; mv a1,s5; jal fuzz_catalogue_row *)
  pl_run_to HS HJ3 AG fpos F EFA3 0x80fb4.
  gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rebv HS E70 RF B70 B75.
  subst k.
  (* the call's registers, the two saved words of the frame chain, through pin_row_site *)
  rreg HS (1%bv : bv 5) Rra. rreg HS (2%bv : bv 5) Rsp. rreg HS (3%bv : bv 5) Rgp. rreg HS (4%bv : bv 5) Rtp.
  rreg HS (8%bv : bv 5) Rs0. rreg HS (10%bv : bv 5) Ra0. rreg HS (11%bv : bv 5) Ra1.
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
    assert (Usp3 : bv_unsigned (ew Ev 2) = spZ regs) by (rewrite (AG 2%nat) by lia; exact Usp) end.
  lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msX) =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let ih := idx_of_base rs 2%nat in let ih := eval vm_compute in ih in
  let rh := eval vm_compute in (nth ih rs got_region) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H W3) msX) ih rh HS ltac:(vm_compute; reflexivity)) as HRstk; cbn [ms_mem restrict] in HRstk;
  lazymatch type of HRstk with region_ok _ _ _ (YP09.mkRegion _ ?lo ?hi ?wlo ?whi ?cs) =>
  pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-8) 8%N (SOff 1 0) (raZ regs) HRstk
    Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 1%nat) by lia; rewrite (EE 1%nat 1%bv eq_refl), Z.add_0_r; reflexivity)
    ltac:(unfold raZ; pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vra;
  pose proof (field_of_region Ex _ 2 (spZ regs) cs lo hi wlo whi (-16) 8%N (SOff 8 0) (s0Z regs) HRstk
    Usp3 ltac:(cbn; tauto) ltac:(cbn [sv_denot ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite (AG 8%nat) by lia; rewrite (EE 8%nat 8%bv eq_refl), Z.add_0_r; reflexivity)
    ltac:(unfold s0Z; pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Hq; change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hq; exact Hq) ltac:(cbn; lia)) as Vs0 end;
  clear HRstk;
  assert (Wra : rdword (aview tfibsegs (w_H W3) (ms_mem msX)) (spZ regs - 8) = Some (raZ regs))
    by (replace (spZ regs - 8) with (spZ regs + -8) by lia; apply rdword_of_val_mem; [exact Vra | unfold raZ; apply unsigned_range_64]);
  assert (Ws0 : rdword (aview tfibsegs (w_H W3) (ms_mem msX)) (spZ regs - 16) = Some (s0Z regs))
    by (replace (spZ regs - 16) with (spZ regs + -16) by lia; apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; apply unsigned_range_64]);
  clear Vra Vs0;
  destruct (pin_row_site (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T) ly3 S3 W3 (ms_mem msX) _ (ms_regs msX) q (colon_idx s)
    HBASE0 HJ3 ltac:(cbn [c_ly c_S c_pl]; fold s; rewrite Hls; exact Hq3) HGq Htl Rra
    ltac:(unfold spZ; rewrite Rsp; exact B70)
    ltac:(rewrite Rgp, (AG 3%nat) by lia; exact (EE 3%nat 3%bv eq_refl))
    ltac:(rewrite Rtp, (AG 4%nat) by lia; exact (EE 4%nat 4%bv eq_refl))
    ltac:(unfold s0Z; rewrite Rs0; exact Usp3) HUP Wra Ws0)
    as (Hkit & Htn & Ht32 & Hq0 & Hq63 & Hgt & Hrat & Hhull & Hamr & Hoffw & Hcat & Hoffs & Hro) end.
  fold s in Htn, Hgt.
  lazymatch type of HS with st_ok _ ?Ex ?ssX (restrict _ ?msX) =>
  rewrite (st_ok_restrict_mkst tfibsegs _ _ _ _ HS eq_refl); cbn [ss_pc];
  eapply SRr_bind;
  [ eapply (TROW LLVMF_STK (spZ regs) FP ly S W mem md [(1, fpos)] ly3 S3 W3 (ms_mem msX) _ 1 (ms_regs msX)
      (rt_ch (mkRTCX ly S W regs mem md p n pl fpos sp1 E0 T)) q (Z.of_nat (colon_idx s)) (firstn (colon_idx s) s) Hkit);
    [ rewrite Ra0, E100; reflexivity | rewrite Ra1, E640; reflexivity | exact Htn | exact Ht32 | exact Hq0 | exact Hq63
    | exact Hgt | exact Hrat | exact Hhull | exact Hamr | exact Hoffw | exact Hcat | exact Hoffs | exact Hro ]
  | ] end.
  cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hfrs4 & HPerm4 & HIO4 & HMLE4 & K1 & HR4).
  lazymatch type of Rsp with getr ?rg 2 = _ => assert (EspX : spZ rg = sp1) by (unfold spZ; rewrite Rsp; exact B70) end.
  rewrite EspX in K1. unfold T_row_STK, ESTACK in K1. rewrite Rra.
  pose proof (mle_station MT S S3 S4 acc 0 MTL HMLE HMLE4) as HMLE4c.
  pose proof (proj1 HJ4) as HAR4.
  destruct (al_layout _ _ LAWS _ _ _ _ _ ly4 HAR (proj1 (proj2 HJ4))) as (_ & EFA4 & _).
  assert (Hfin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4; exact Hfin3).
  assert (Hfrs4' : frames S4 = [(1, fpos)]) by (rewrite Hfrs4; exact Hfrs3).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR4 Hfin4) as (_ & _ & HFpres4 & HFSpres4).
  change (fs_frame_bytes 1) with 128 in HFpres4, HFSpres4. change (128 / 8) with 16 in HFSpres4.
  rewrite !EFA4 in HFpres4, HFSpres4. fold F in HFpres4, HFSpres4.
  pose proof HJ4 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres4 & _).
  assert (HUP4 : forall a, spZ regs <= a < 2 ^ 64 -> aview tfibsegs (w_H W4) mem4 a = aview tfibsegs (w_H W) mem a).
  { intros a Ha. rewrite <- (HUP a Ha). apply K1; [lia | lia | intros []]. }
  clear HUP; rename HUP4 into HUP.
  lazymatch type of HGq with garr8 _ (mrestrict _ ?m3) _ _ =>
  assert (HGq4 : garr8 tfibsegs (mrestrict (w_H W4) mem4) q (pin_zbytes s ++ [0]))
  by (apply (pm3_garr8_kept (w_H W3) (w_H W4) m3 mem4 q _); [|exact HGq];
      intros j Hj; rewrite pm3_zb_len in Hj; apply K1; [lia | lia | intros []]) end.
  clear HGq; rename HGq4 into HGq.
  reseatL HS HJ4 HP4 [0; 1; 2]%nat AG
  ltac:(idtac; lazymatch goal with |- region_kept _ _ _ _ (YP09.mkRegion (Some ?nb) _ _ _ _ _) =>
    eapply pm3_region_kept_eq; [ evalE AG
    | intros a Ha; apply K1; [lia | unfold SB in *; lia | intros []]
    | intros a Ha; first [ exfalso; lia | apply (proj1 (HFpres4 a ltac:(lia))) | apply Hpres4; lia ] ] end).
  relowRT HS AG E10 E11 E32 E10n E11n E32n. norm_ss HS. rebv HS E70 RF B70 B75.
  assert (Hq4 : In (q, kk + 1) (ablocks B ly4 S4)) by (eapply Permutation_in; [apply Permutation_sym; exact HPerm4 | exact Hq3]).
  rreg HS (10%bv : bv 5) Ra0r. rewrite HR4 in Ra0r.
  assert (Hwant : harness_want fl s = row_of (firstn (colon_idx s) s)).
  { unfold harness_want. rewrite (proj2 (Z.eqb_eq _ _) Hc1).
    destruct (Nat.eqb_spec (length s) 0) as [Hs0|Hs0]; [lia | reflexivity]. }
  unfold COLON in Hcc.
  destruct (row_of (firstn (colon_idx s) s)) as [i|] eqn:Hrow; unfold row_ptr in Ra0r; rewrite Hrow in Ra0r.
  + (* the token names row i: want = &table[i] *)
    destruct (row_of_some _ _ Hrow) as (Hi & _ & _).
    assert (HPC : PIN_CAT = 622592) by reflexivity.
    assert (Hrb : 622592 <= row_addr PIN_CAT i <= 625552) by (unfold row_addr, CAT_ROW, CAT_N in *; lia).
    add_atom_win HS 104%nat (Z_to_bv 64 (row_addr PIN_CAT i)) E104.
    pin_by HS (10%bv : bv 5) (SOff 104 0) ltac:(rewrite !sv_denot_SOff0, E104; ewpeel; rewrite <- Ra0r; reflexivity).
    (* the range of slot 104 and its alignment 8 (want = row_addr cat i, cat mod 8 = 0): the executor computes
       want & 7 = 0 at 0x80a94, so the trap branch 0x80a98 is decided not taken *)
    lazymatch type of HS with st_ok _ ?Ev ?ssx ?msx =>
      let HS3 := fresh "HS3" in
      pose proof (st_ok_add_fact tfibsegs Ev ssx msx 104%nat (mkAF 622592 625552 3) HS
        ltac:(clear HS; unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E104, unsigned_lit_small by lia;
              change (2 ^ 3) with 8; split; [lia | split; [apply row_addr_mod8; reflexivity | clear; lia]])) as HS3;
      clear HS; rename HS3 into HS end.
    (* 0x80a54 beqz a0 (not taken); 0x80a58 mv s4,a0; li a0,':'; stop at bne s6,a0 *)
    pl_run HS HJ4 AG fpos F EFA4.
    gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    br_split HS Hc3.
    all: hc_bool Hc3 ltac:(fun H => hc_atom H 641%nat c E641 ltac:(lia)); hc_prop Hc3.
    * (* s6 <> ':': tok = len, 0x80a94: want & 7 = 0 (the trap branch 0x80a98 not taken), want->display *)
      assert (Hce : colon_idx s = length s) by (destruct (Nat.lt_ge_cases (colon_idx s) (length s)) as [Hl|Hl];
        [exfalso; apply Hc3; apply Hcc; exact Hl | lia]).
      assert (Hlab : harness_label_off s = None)
        by (unfold harness_label_off; rewrite (proj2 (Nat.ltb_ge (colon_idx s) (length s)) ltac:(lia)); reflexivity).
      lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?mx _ _ =>
      assert (HRO5 : arodata_okP tfibsegs PM_RLO PM_RHI B (aview tfibsegs (w_H Wx) mx))
        by (apply pm_arodataP; exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HROD));
      assert (HCAT5 : pin_cat_ok tfibsegs (mrestrict (w_H Wx) mx) (aview tfibsegs (w_H Wx) mx) PM_CAT PM_TP PM_DP)
        by (eapply proj1; eapply pin_ro_law_at; [exact FCAT | exact HJ4 | exact HRO5]) end.
      destruct HCAT5 as (_ & _ & _ & _ & HRAc & Hrows).
      destruct (Hrows i Hi) as (_ & Vdp & _ & Rdp & _); clear Hrows HRO5.
      add_atom_win HS 105%nat (Z_to_bv 64 (PIN_DP i)) E105.
      tab_region HS AG E104 E105 Vdp Rdp.
      rd_run_tab_to HS HJ4 AG fpos F EFA4 E104 E32n HRAc 0x808f0.
      gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      ra_join_win HS ss_D 700%nat pm_D_deads_bv ltac:(idtac).
      rb HS AG E10 E11 E32 E10n E11n E32n.
      rt_hand RD HS. fold s.
      split; [unfold EV_row; lia|]. split; [lia|].
      exists q, fl, (row_addr PIN_CAT i), (PIN_DP i).
      repeat match goal with |- _ /\ _ => split end;
      first [ eassumption | (rewrite <- Hkk, <- Eab3; exact HPerm4) | (unfold pm_want; rewrite Hwant; try rewrite Hrow; reflexivity)
            | (unfold pm_wlab; rewrite Hwant; try rewrite Hrow; rewrite Hlab; reflexivity) ].
    * (* s6 = ':': tok < len *)
      assert (Hlt : (colon_idx s < length s)%nat) by (apply Hcc; lia).
      (* 0x80a60 bne (not taken: s6 = ':'); the run stops at the trap branch 0x80a64 bgeu s5,s11: tok < len < 2 ^ 64
         - 1 - q = ~q, so it is not taken *)
      pl_run HS HJ4 AG fpos F EFA4.
      gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      br_split HS Ht2.
      all: hc_bool Ht2 ltac:(fun H => hc_atom H 640%nat (Z.of_nat (colon_idx s)) E640 ltac:(clear - Htl Hls Hq4096 Hqceil Hkk0 C1; lia);
        hc_atom H 106%nat (2 ^ 64 - 1 - q) E106 ltac:(clear - Hq4096 Hqceil Hkk0 C1; lia)); hc_prop Ht2.
      1: exfalso; clear - Ht2 Htl Hls Hq4096 Hqceil Hkk0 C1; lia.
      clear Ht2. norm_ss HS.
      (* 0x80a68 add a0,s3,s5: a0 = q + tok, pinned to slot 663 with its range *)
      pl_run_to HS HJ4 AG fpos F EFA4 0x80a6c.
      gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      add_atom_win HS 663%nat (Z_to_bv 64 (q + Z.of_nat (colon_idx s))) E663.
      pin_by HS (10%bv : bv 5) (SOff 663 0) ltac:(rewrite sv_denot_SOff0, E663, denot_lit_U; f_equal;
        rewrite U_SAlu; cbn [zalu_raw];
        rewrite (U_atom _ 100 q) by first [ewpeel; eassumption | lia];
        rewrite (U_atom _ 640 (Z.of_nat (colon_idx s))) by first [ewpeel; eassumption | lia];
        rewrite zcanon_id by (unfold M64; lia); lia).
      add_fact HS 663%nat 4096 140737479966720 E663 ltac:(lia).
      (* 0x80a6c addi s5,a0,1: s5 = q + tok + 1, pinned to slot 661 *)
      pl_run_to HS HJ4 AG fpos F EFA4 0x80a70.
      gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      add_atom_win HS 661%nat (Z_to_bv 64 (q + 1 + Z.of_nat (colon_idx s))) E661.
      pin_by HS (21%bv : bv 5) (SOff 661 0) ltac:(rewrite sv_denot_SOff0, E661, (denot_lit_U _ (SOff 663 1)); f_equal;
        rewrite (U_atom_off _ 663 (q + Z.of_nat (colon_idx s)) 1) by first [ewpeel; exact E663 | lia]; lia).
      add_fact HS 661%nat 4096 140737479966720 E661 ltac:(lia).
      assert (Hd1 : (Datatypes.S (colon_idx s) < length (pin_zbytes s ++ [0%Z]))%nat) by (rewrite pm3_zb_len; lia).
      destruct (HGq _ Hd1) as (Vd & Rd).
      set (d := nth (Datatypes.S (colon_idx s)) (pin_zbytes s ++ [0]) 0) in Vd, Rd.
      replace (q + Z.of_nat (Datatypes.S (colon_idx s))) with (q + 1 + Z.of_nat (colon_idx s)) in Vd by lia.
      add_atom_win HS 662%nat (Z_to_bv 64 d) E662.
      add_fact HS 662%nat 0 255 E662 ltac:(lia).
      in_region_v HS (YP09.mkRegion (Some 661%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 662 0))]) E661 Vd Rd E662 AG idtac.
      (* 0x80a70-0x80a80: the check of q + tok + 1 (slow path 0x80ae4, error 0x80af0 not reached), lbu a1,0(s5);
         stop at beqz a1 *)
      rd_run_q HS HJ4 AG fpos F EFA4 E661 E32n Hq4 Hrq.
      gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
      rb HS AG E10 E11 E32 E10n E11n E32n.
      assert (Hdv : d = bv_unsigned (nth (Datatypes.S (colon_idx s)) (s ++ [NUL]) NUL)) by (unfold d; apply pm3_zb_nth).
      br_split HS Hc4.
      all: hc_bool Hc4 ltac:(fun H => hc_atom H 662%nat d E662 ltac:(lia)); hc_prop Hc4.
      -- (* q[tok + 1] = 0: 0x80a94, want & 7 = 0 (the trap branch 0x80a98 not taken), want->display *)
         assert (Hlab : harness_label_off s = None).
         { unfold harness_label_off. rewrite (proj2 (Nat.ltb_lt _ _) Hlt), <- Hdv, Hc4. reflexivity. }
         lazymatch type of HJ4 with ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ ?Wx ?mx _ _ =>
         assert (HRO5 : arodata_okP tfibsegs PM_RLO PM_RHI B (aview tfibsegs (w_H Wx) mx))
           by (apply pm_arodataP; exact (arodata_ok_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ4 HROD));
         assert (HCAT5 : pin_cat_ok tfibsegs (mrestrict (w_H Wx) mx) (aview tfibsegs (w_H Wx) mx) PM_CAT PM_TP PM_DP)
           by (eapply proj1; eapply pin_ro_law_at; [exact FCAT | exact HJ4 | exact HRO5]) end.
         destruct HCAT5 as (_ & _ & _ & _ & HRAc & Hrows).
         destruct (Hrows i Hi) as (_ & Vdp & _ & Rdp & _); clear Hrows HRO5.
         add_atom_win HS 105%nat (Z_to_bv 64 (PIN_DP i)) E105.
         tab_region HS AG E104 E105 Vdp Rdp.
         rd_run_tab_to HS HJ4 AG fpos F EFA4 E104 E32n HRAc 0x808f0.
         gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
         rb HS AG E10 E11 E32 E10n E11n E32n.
         ra_join_win HS ss_D 700%nat pm_D_deads_bv ltac:(idtac).
         rb HS AG E10 E11 E32 E10n E11n E32n.
         rt_hand RD HS. fold s.
         split; [unfold EV_row; lia|]. split; [lia|].
         exists q, fl, (row_addr PIN_CAT i), (PIN_DP i).
         repeat match goal with |- _ /\ _ => split end;
         first [ eassumption | (rewrite <- Hkk, <- Eab3; exact HPerm4) | (unfold pm_want; rewrite Hwant; try rewrite Hrow; reflexivity)
               | (unfold pm_wlab; rewrite Hwant; try rewrite Hrow; rewrite Hlab; reflexivity) ].
      -- (* q[tok + 1] <> 0: want_label = q + tok + 1; 0x80a88 a1 = -1, 0x80a8c bne a0,a1 decided taken (slot 663 lies in
            [4096, 2 ^ 47 - 2 ^ 23], so a0 <> 2 ^ 64 - 1 and the trap 0x80a90 is not reached); to 0x808f0 *)
         assert (Hlab : harness_label_off s = Some (Datatypes.S (colon_idx s))).
         { unfold harness_label_off. rewrite (proj2 (Nat.ltb_lt _ _) Hlt), <- Hdv, (proj2 (Z.eqb_neq _ _) Hc4). reflexivity. }
         pl_run_to HS HJ4 AG fpos F EFA4 0x808f0.
         gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
         rb HS AG E10 E11 E32 E10n E11n E32n.
         add_atom_win HS 105%nat (Z_to_bv 64 (q + Z.of_nat (Datatypes.S (colon_idx s)))) E105.
         pin_by HS (21%bv : bv 5) (SOff 105 0) ltac:(rewrite !sv_denot_SOff0, E105; ewpeel; rewrite E661; f_equal; lia).
         ra_join_win HS ss_D 700%nat pm_D_deads_bv ltac:(idtac).
         rb HS AG E10 E11 E32 E10n E11n E32n.
         rt_hand RD HS. fold s.
         split; [unfold EV_row; lia|]. split; [lia|].
         exists q, fl, (row_addr PIN_CAT i), (q + Z.of_nat (Datatypes.S (colon_idx s))).
         repeat match goal with |- _ /\ _ => split end;
         first [ eassumption | (rewrite <- Hkk, <- Eab3; exact HPerm4) | (unfold pm_want; rewrite Hwant; try rewrite Hrow; reflexivity)
               | (unfold pm_wlab; rewrite Hwant; try rewrite Hrow; rewrite Hlab; reflexivity) ].
  + (* no row: want = 0 *)
    add_atom_win HS 104%nat (Z_to_bv 64 0) E104.
    pin_by HS (10%bv : bv 5) (SOff 104 0) ltac:(rewrite !sv_denot_SOff0, E104; ewpeel; rewrite <- Ra0r; reflexivity).
    (* 0x80a54 beqz a0 (taken); 0x808e8 s4 = s5 = 0; to 0x808f0 *)
    br_split HS Hc2.
    all: hc_bool Hc2 ltac:(fun H => hc_atom H 104%nat 0 E104 ltac:(lia)); hc_prop Hc2.
    2: { exfalso. lia. }
    pl_run_to HS HJ4 AG fpos F EFA4 0x808f0.
    gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
    rb HS AG E10 E11 E32 E10n E11n E32n.
    pin_by HS (20%bv : bv 5) (SOff 104 0) ltac:(rewrite sv_denot_SOff0, E104; reflexivity).
    add_atom_win HS 105%nat (Z_to_bv 64 0) E105.
    pin_by HS (21%bv : bv 5) (SOff 105 0) ltac:(rewrite sv_denot_SOff0, E105; reflexivity).
    ra_join_win HS ss_D 700%nat pm_D_deads_bv ltac:(idtac).
    rb HS AG E10 E11 E32 E10n E11n E32n.
    rt_hand RD HS. fold s.
    split; [unfold EV_row; lia|]. split; [lia|].
    exists q, fl, 0, 0.
    repeat match goal with |- _ /\ _ => split end;
    first [ eassumption | (rewrite <- Hkk, <- Eab3; exact HPerm4) | (unfold pm_want, pm_wlab; rewrite Hwant; try rewrite Hrow; reflexivity) ].
- (* flags & 7 <> 0: 0x808e8 s4 = 0, s5 = 0, to ss_D *)
  pl_run_to HS HJ3 AG fpos F EFA3 0x808f0.
  gkeep HGq AG. upd_aboveW HUP HFr AG. clear_frames.
  rb HS AG E10 E11 E32 E10n E11n E32n.
  add_atom_win HS 104%nat (Z_to_bv 64 0) E104.
  pin_by HS (20%bv : bv 5) (SOff 104 0) ltac:(rewrite sv_denot_SOff0, E104; reflexivity).
  add_atom_win HS 105%nat (Z_to_bv 64 0) E105.
  pin_by HS (21%bv : bv 5) (SOff 105 0) ltac:(rewrite sv_denot_SOff0, E105; reflexivity).
  ra_join_win HS ss_D 700%nat pm_D_deads_bv ltac:(idtac).
  rb HS AG E10 E11 E32 E10n E11n E32n.
  rt_hand RD HS. fold s.
  split; [exact Hk|]. split; [exact Hacc|].
  assert (Hw : harness_want fl s = None) by (unfold harness_want; rewrite (proj2 (Z.eqb_neq _ _) Hc1); reflexivity).
  exists q, fl, 0, 0.
  repeat match goal with |- _ /\ _ => split end;
  first [ eassumption | (unfold pm_want, pm_wlab; rewrite Hw; reflexivity) | (rewrite Eab3, <- Hkk; apply Permutation_refl) | lia ].
Qed.

(* S3: ss_C (0x80868) -> ss_D (0x808bc) *)
Lemma pm_S3 : rt_from B MT FP POST ss_D (INV_D B MT) -> rt_from B MT FP POST ss_C (INV_C B MT).
Proof. intros RD. exact (pm_S3_entry (pm_S3_loop (pm_S3_post RD))). Qed.
End d.
End c.
