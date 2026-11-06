(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the loop segment of answer's ASan walk (plugin-hostd/fuzz_command, 0x8a4c0):
   syntax_instantiate's loop from its head HEAD (0x8a670) to JOIN (0x8a734), an_head_ok : AN_JOIN_stmt ->
   AN_HEAD_stmt (lib/A/Prog/answer_s1.v), by strong induction on the bytes of the shape left, in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/AC8b.v (tcbb_loopX, a loop with inline checks, re-seeded at each iteration). The
   plain proof of the same loop is lib/Prog/answer.v:120-226 (an_loop). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/answer_l.v, with its module paths, module names and numbers changed; 595 of its 672 lines of code are new or changed and 710 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): stretch SA9_C of segment A9 of reac_segconf_parse_file's walk
   (lib/A/Prog/pf_a9_d.v: K3 0x87ff4 -> K5 0x8814c), a9_sC : SA9_C B. By the G3 walk owner, 2026-10-30.
   proves no function (kind: segment lemma of reac_segconf_parse_file's image-A walk, one stretch of segment A9; the
   whole function's rule-24 line, its pasted released-proof index output and the G3 walk owner's CONFIRM of
   2026-10-30T15:42:08Z are in the unit's internal record, commit dfb49d6ad789,
   path records/segp/g3-lookup.md, reuse verdict none: written
   new).

   THE CODE (the excerpt reac_segconf_parse_file.fuzz_segconf.asan.s in records/segp/dis/ at that commit;
   reac_segconf.c:78-86, unquote inlined; no call):
     0x87ff4 addi a1,zero,2; bltu a0,a1,0x880a4         |v| < 2: 0x880a4 ld s8,0x90(s1); j 0x8814c
     0x87ffc check 10 (load1 at s9 = vp0); 0x88008 ld s8,0x90(s1); 0x88010 lbu a1,0(s9); beq a1,SQ,0x88108
     0x8801c bne a1,DQ,0x8814c; 0x88024 a1 = s9 + a0 - 1; check 11; lbu a1,0(a1); beq a1,DQ,0x8812c; j 0x8814c
     0x88108 a1 = s9 + a0 - 1; check 14; lbu a1,0(a1); bne a1,SQ,0x8814c
     0x8812c a0 = s9 + a0 - 1; check 15 (store1); 0x88144 sb zero,0(a0); 0x88148 addi s9,s9,1; 0x8814c K5
   THE ROUTE (fuzz_command's answer_l.v al_entry / al_SH form at origin/ossv/recipes 501c0d516c69, its trim_t.v twin
   in this clone): each arm re-seeds a symbolic state at K3 from INV_K3's concrete facts and runs the TOKEN executor
   (SegPaLib.v paj_run_tok, Bx = SOff 22 0 = s6, pf_fi's SHADOW_OFF). The two byte reads are DECIDED by REGIONS with
   one-byte CVal chunks (chain_words_s2.v cw2_seedC's route, chunk_ok from a9_inbuf's sa_str): atom 33 = V[0] in a
   read-only region on s9's atom 25, atom 35 = V[|V| - 1] in a one-byte WRITABLE region on atom 34 = vp0 + |V| - 1,
   which the facts' alias (s9 + a0 = atom 34 + 1) names, so that `add a1,s9,a0; addi a1,a1,-1` lands on it. The
   four checks pass with no obligation: the shadow entries [mkSHE 25 0 1; mkSHE 34 0 1] cover their bytes, from
   pf_a9_f.v's a9_buf_addr (buf in scope under PF_SC_LINE). s8 = c comes from a read-only region over slot 0x90 of
   PF_SL (atom 32 = c). |v| < 2 is its own seed (no byte region; atom 10's fact [0, 1] decides the bltu).
   After the run the cut K5 is rebuilt by pf_a5_k.v's a5_move0 / a5_keep_st / a5_keep_slot / a5_keep_fsh at the
   one written byte (the unquote NUL, inside buf = a5_Wrx's buf clause); the key's string lies below vp0
   (INV_K3's kp + |key| < vp0), so it survives the store. No Section hypothesis is used. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegAddr SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase refuse_c
  reac_segconf_parse_file_c SegInstA pf_pieces pf_a9_d pf_a9_f pf_a5_d pf_a5_k.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================= the symbolic states at K3 ======================= *)
(* s6 (x22) holds the shadow base (pf_fi's (22, SHADOW_OFF)); slot 0x90 of s1 holds c (PF_SL, atom 32) *)
Definition s3_Bx : sv := SOff 22 0.
Definition s3_slot : YP09.region := YP09.mkRegion (Some 9%nat) 0x90 0x98 0 0 [YP09.mkChunk 0x90 (CVal 8 (SOff 32 0))].
(* |v| < 2: the slot only; atom 10 = a0 = |v| in [0, 1] decides `bltu a0, 2` *)
Definition s3_rgA : smem := [ s3_slot ].
Definition s3_fA : facts := mkFacts [ (22%nat, mkAF SB SB 0); (10%nat, mkAF 0 1 0) ] [] [].
Definition s3_ssA : sstate := mkSS A9_K3 sr_atoms s3_rgA None s3_fA.
(* |v| >= 2: the slot, v's first byte (atom 33) at s9 = vp0 (atom 25), v's last byte (atom 35) at atom 34 =
   vp0 + |v| - 1 (written by the strip); the alias says s9 + a0 = atom 34 + 1 *)
Definition s3_rgB : smem :=
[ s3_slot;
  YP09.mkRegion (Some 25%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))];
  YP09.mkRegion (Some 34%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))] ].
Definition s3_fB : facts :=
mkFacts [ (22%nat, mkAF SB SB 0); (25%nat, PTR 0); (10%nat, mkAF 2 511 0); (34%nat, PTR 0);
          (33%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0) ]
[] [ (SAlu ALU_ADD (SOff 25 0) (SOff 10 0), SOff 34 1) ].
Definition s3_ssB : sstate := mkSS A9_K3 sr_atoms s3_rgB None s3_fB.
(* the shadow entries of checks 10 (vp0) and 11 / 14 / 15 (vp0 + |v| - 1) *)
Definition s3_SHB : list shent := [mkSHE 25 0 1; mkSHE 34 0 1].
(* the registers no run of the stretch writes (the run writes a0..a3, s8, s9) *)
Definition S3_KZ : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 26; 27]%Z.
Definition S3_KEPT : list (bv 5) := map (Z_to_bv 5) S3_KZ.

(* ======================= pure facts ======================= *)
Lemma s3_ex : forall z : Z, exists y, z = y.
Proof. intros z. exists z. reflexivity. Qed.
Lemma s3_mod8 : forall F, F mod 32 = 0 -> F mod 8 = 0.
Proof.
intros F H. apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. rewrite Hk.
replace (k * 32) with ((4 * k) * 8) by lia. apply Z_mod_mult.
Qed.
Lemma s3_zs_nth : forall (rd : reader) p (s : list Z) i, sa_zs rd p (s ++ [0]) -> (i < length s)%nat ->
  rd (p + Z.of_nat i) = Some (nth i s 0).
Proof.
intros rd p s i H Hi. rewrite (H i) by (rewrite length_app; cbn [length]; lia). rewrite app_nth1 by exact Hi.
reflexivity.
Qed.
(* a C string whose bytes and NUL are kept *)
Lemma s3_str_keep : forall (rd rd' : reader) p s, sa_str rd p s ->
  (forall a, p <= a <= p + Z.of_nat (length s) -> rd' a = rd a) -> (forall a, rd a <> None -> rd' a <> None) ->
  sa_str rd' p s.
Proof.
intros rd rd' p s ((HZ & NZ) & HT) KM KP. split; [split; [|exact NZ]|].
- intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. rewrite KM by lia. apply HZ.
  rewrite length_app. cbn [length]. lia.
- intros y Hy. apply KP. exact (HT y Hy).
Qed.
(* the strip: V's bytes with a NUL at index |V| - 1 are the C string slice 1 (|V| - 1) V at p + 1 *)
Lemma s3_str_strip : forall (rd rd' : reader) p V P,
  sa_str rd p V -> (2 <= length V)%nat -> P = p + Z.of_nat (length V) - 1 ->
  (forall a, p <= a <= p + Z.of_nat (length V) -> a <> P -> rd' a = rd a) -> rd' P = Some 0 ->
  (forall a, rd a <> None -> rd' a <> None) ->
  sa_str rd' (p + 1) (slice 1 (length V - 1) V).
Proof.
intros rd rd' p V P ((HZ & NZ) & HT) Hl HP KM H0 KP.
assert (HL : length (slice 1 (length V - 1) V) = (length V - 2)%nat)
  by (unfold slice; rewrite length_firstn, length_skipn; lia).
assert (HN : forall i, (i < length V - 2)%nat -> nth i (slice 1 (length V - 1) V) 0 = nth (S i) V 0).
{ intros i Hi. unfold slice. rewrite nth_firstn.
  destruct (Nat.ltb_spec i (length V - 1 - 1)) as [_|]; [|lia].
  rewrite nth_skipn. f_equal. }
split; [split|].
- intros i Hi. rewrite length_app, HL in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length V - 2)) as [Hlt | Hge].
  + rewrite app_nth1 by (rewrite HL; exact Hlt). rewrite (HN i Hlt).
    rewrite KM by lia.
    replace (p + 1 + Z.of_nat i) with (p + Z.of_nat (S i)) by lia.
    exact (s3_zs_nth rd p V (S i) HZ ltac:(lia)).
  + assert (i = length V - 2)%nat as -> by lia.
    rewrite app_nth2 by (rewrite HL; lia). rewrite HL, Nat.sub_diag. cbn [nth].
    replace (p + 1 + Z.of_nat (length V - 2)) with P by lia. exact H0.
- intros Hin. apply NZ. unfold slice in Hin. exact (a9_in_skipn 1 V 0 (a9_in_firstn _ _ _ Hin)).
- rewrite HL. intros y Hy.
  replace (p + 1 + Z.of_nat (length V - 2)) with P in Hy by lia.
  apply KP. destruct (Z.eq_dec y (p + Z.of_nat (length V))) as [-> | Hne].
  + rewrite (HZ (length V)) by (rewrite length_app; cbn [length]; lia). discriminate.
  + apply HT.
    pose proof (Z.div_mod P 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound P 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (p + Z.of_nat (length V)) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (p + Z.of_nat (length V)) 8 ltac:(lia)) as M2.
    assert (Q : P / 8 <= (p + Z.of_nat (length V)) / 8) by (apply Z.div_le_mono; lia).
    lia.
Qed.
(* the token runs' branch tests on an atom of known value (fuzz_command's answer_l.v al_br_eq) *)
Lemma s3_br_eq : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> (v =? z) = b.
Proof. intros E n v z b H Hv Hz Hc. rewrite branch_eq_U, (U_atom E n v H Hv), U_lit in Hc by exact Hz. exact Hc. Qed.
Lemma s3_br_ne : forall E n v z b, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit z)) = b -> negb (v =? z) = b.
Proof. intros E n v z b H Hv Hz Hc. rewrite branch_ne_U, (U_atom E n v H Hv), U_lit in Hc by exact Hz. exact Hc. Qed.
Lemma s3_den_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c H Hv. cbn [sv_denot]. rewrite H, unsigned_lit_small by exact Hv. reflexivity. Qed.
Lemma s3_byte_atom : forall E n z, ew E n = Z_to_bv 64 z -> 0 <= z < 256 ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 256 = z.
Proof.
intros E n z H Hz. change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
rewrite (U_atom E n z H) by lia. apply Z.mod_small. lia.
Qed.
(* environments that agree below 36 (answer_l.v al_ag32 / al_ag_ew) *)
Lemma s3_ag32 : forall (regs1 : bvmap 5 word) extra E0 E,
  env_agree 32 (Ereg regs1 extra) E0 -> env_agree 36 E0 E -> env_agree 32 (Ereg regs1 extra) E.
Proof. intros regs1 extra E0 E H0 H1. eapply env_agree_trans; [exact H0 | eapply env_agree_le; [|exact H1]; lia]. Qed.
Lemma s3_ag_ew : forall E0 E n v, env_agree 36 E0 E -> (n < 36)%nat -> ew E0 n = Z_to_bv 64 v -> ew E n = Z_to_bv 64 v.
Proof. intros E0 E n v H Hn H0. rewrite (proj1 H n Hn). exact H0. Qed.
(* a pf_rg list of registers that a step keeps *)
Lemma s3_rg_keep : forall (rX rX' : bvmap 5 word) L,
  (forall r, In r (map fst L) -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)) -> pf_rg rX L -> pf_rg rX' L.
Proof.
unfold pf_rg. intros rX rX' L HK H. rewrite Forall_forall in *. intros rv Hin.
rewrite HK by (apply in_map; exact Hin). exact (H rv Hin).
Qed.

Ltac s3_inz := unfold S3_KZ; cbn [In]; repeat (first [left; reflexivity | right]).
Ltac s3_win :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b wlo whi a' Hin Hrr; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]);
  destruct Hin.
(* a register's value after a run, without prreg's normalisation *)
Ltac s3_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a mapped byte stays mapped when the memory grows *)
Lemma s3_view_grows : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> aview SEGS H m a <> None -> aview SEGS H m' a <> None.
Proof.
intros H m m' a G Hn. unfold aview, mbyte in *.
destruct (mrestrict H m (Z_to_bv 64 a)) as [b|] eqn:E1.
- pose proof (G (Z_to_bv 64 a)) as G1. rewrite E1 in G1. specialize (G1 ltac:(discriminate)).
  destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|] eqn:E2; [discriminate | exfalso; exact (G1 eq_refl)].
- destruct (mrestrict H m' (Z_to_bv 64 a)) as [b'|]; [discriminate | exact Hn].
Qed.
(* a run writes at most the byte P (answer_l.v al_keep_step, any window list) *)
Lemma s3_keep_step : forall E rs (H : word -> bool) (m m' m0 : word -> option byte) P,
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> a = P) ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> P -> aview SEGS H m a = aview SEGS H m0 a) ->
  forall a, 0 <= a < 2 ^ 64 -> a <> P -> aview SEGS H m' a = aview SEGS H m0 a.
Proof.
intros E rs H m m' m0 P HFr HW KM a Ha Hn.
rewrite (kept_of_frame (segs := SEGS) E rs H m m' (fun a' => a' = P) HFr HW a Ha Hn). exact (KM a Ha Hn).
Qed.
(* the byte a run wrote into a one-byte written region (lib/A/Prog/trim_t.v tr_wbyte, from fuzz_command's
   answer_l.v al_wbyte) *)
Lemma s3_wbyte : forall E ss ms (H : word -> bool) (n i : nat) Pz v,
  st_ok_pi SEGS VAL E ss (restrict H ms) ->
  nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some n) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 v)]) ->
  bv_unsigned (ew E n) = Pz ->
  aview SEGS H (ms_mem ms) Pz = Some (bv_unsigned (sv_denot E v) mod 256).
Proof.
intros E ss ms H n i Pz v HS Hn HP.
pose proof (st_ok_pi_region_nth E ss (restrict H ms) i _ HS Hn) as Hr.
pose proof (field_of_region_any E _ n Pz _ 0 1 0 1 0 1%N v Hr HP (or_introl eq_refl) ltac:(lia)) as V.
cbn [ms_mem restrict] in V. rewrite Z.add_0_r in V. change (2 ^ (8 * Z.of_N 1)) with 256 in V.
apply aview_of_val_mem1; [exact V | apply Z.mod_pos_bound; lia].
Qed.

(* ---- the seeds ---- *)
Definition s3_EA (rX : bvmap 5 word) (c : Z) : env := Eimg (Ereg rX [Z_to_bv 64 c]).
Definition s3_EB (rX : bvmap 5 word) (c V0 P VL : Z) : env :=
  Eimg (Ereg rX [Z_to_bv 64 c; Z_to_bv 64 V0; Z_to_bv 64 P; Z_to_bv 64 VL]).

Lemma s3_entryA : forall (W : world SEGS) (rX : bvmap 5 word) memc s1 nV c,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF -> getr rX (Z_to_bv 5 10) = w64 nV ->
  0 <= s1 -> s1 + 0x98 <= 2 ^ 64 -> 0 <= c < 2 ^ 64 -> 0 <= nV <= 1 ->
  rdword (rdW W memc) (s1 + 0x90) = Some c ->
  st_ok_pi SEGS VAL (s3_EA rX c) s3_ssA (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + A9_K3)) memc (seg_rom SEGS))).
Proof.
intros W rX memc s1 nV c H9 H22 H10 Hs0 Hs1 Hc HnV Hslot.
assert (E9 : ew (s3_EA rX c) 9 = Z_to_bv 64 s1)
  by (unfold s3_EA; rewrite (ew_Eimg_Ereg_nat rX _ 9 (Z_to_bv 5 9) eq_refl); exact H9).
assert (E22 : ew (s3_EA rX c) 22 = Z_to_bv 64 SB)
  by (unfold s3_EA; rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl); exact H22).
assert (E10 : ew (s3_EA rX c) 10 = Z_to_bv 64 nV)
  by (unfold s3_EA; rewrite (ew_Eimg_Ereg_nat rX _ 10 (Z_to_bv 5 10) eq_refl); exact H10).
assert (E32 : ew (s3_EA rX c) 32 = Z_to_bv 64 c)
  by (unfold s3_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
rewrite restrict_mkst_fx. unfold s3_ssA. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s3_rgA, s3_slot. constructor; [|constructor].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS (s3_EA rX c) _ s1 0x90 8%N (SOff 32 0) c);
    [| lia | lia | exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hslot)].
  cbn [sv_denot]. rewrite E32, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
- cbn. tauto.
- split; [|split; exact I].
  cbn [s3_fA f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E22, E10, !unsigned_lit_small by (unfold SB; lia).
  rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
Qed.

Lemma s3_entryB : forall (W : world SEGS) (rX : bvmap 5 word) memc s1 vp0 nV c V0 P VL,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF ->
  getr rX (Z_to_bv 5 25) = w64 vp0 -> getr rX (Z_to_bv 5 10) = w64 nV ->
  0 <= s1 -> s1 + 0x98 <= 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  4096 <= vp0 -> vp0 + 1 <= P -> P <= 140737479966720 -> 2 <= nV <= 511 -> P + 1 = vp0 + nV ->
  0 <= V0 <= 255 -> 0 <= VL <= 255 -> P + 1 <= s1 + 0x90 ->
  rdword (rdW W memc) (s1 + 0x90) = Some c ->
  rdW W memc vp0 = Some V0 -> rdW W memc P = Some VL -> apresent (w_H W) memc P ->
  st_ok_pi SEGS VAL (s3_EB rX c V0 P VL) s3_ssB
    (restrict (w_H W) (mkst rX (Z_to_bv 64 (BASE + A9_K3)) memc (seg_rom SEGS))).
Proof.
intros W rX memc s1 vp0 nV c V0 P VL H9 H22 H25 H10 Hs0 Hs1 Hc Hv0 HvP HP HnV HPn HV0 HVL Hdisj Hslot Hb0 HbP HpP.
set (E := s3_EB rX c V0 P VL).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; unfold s3_EB; apply ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 4)%nat ->
  ew E (32 + j) = nth j [Z_to_bv 64 c; Z_to_bv 64 V0; Z_to_bv 64 P; Z_to_bv 64 VL] (Z_to_bv 64 0))
  by (intros j Hj; subst E; unfold s3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
cbn [Nat.add nth] in E32, E33, E34, E35. clear EX.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); exact H9).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); exact H22).
assert (E25 : ew E 25 = Z_to_bv 64 vp0) by (rewrite (EE 25%nat (Z_to_bv 5 25) eq_refl); exact H25).
assert (E10 : ew E 10 = Z_to_bv 64 nV) by (rewrite (EE 10%nat (Z_to_bv 5 10) eq_refl); exact H10).
rewrite restrict_mkst_fx. unfold s3_ssB. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold s3_rgB, s3_slot. constructor; [|constructor; [|constructor; [|constructor]]].
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ s1 0x90 8%N (SOff 32 0) c);
      [| lia | lia | exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hslot)].
    cbn [sv_denot]. rewrite E32, unsigned_lit_small, Z.add_0_r by lia. reflexivity.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E25, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc vp0 V0 Hb0) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E33.
      rewrite !Z.add_0_r, (unsigned_lit_small V0), (unsigned_lit_small V0) by lia. change (8 * 0) with 0.
      rewrite Z.shiftr_0_r. subst V0. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
  + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E34, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; assert (o = 0) as -> by lia; rewrite Z.add_0_r; apply (apresent_writable SEGS); exact HpP|].
    constructor; [|constructor].
    unfold YP09.chunk_ok, YP09.c_len, YP09.cv_len. cbn [YP09.c_off YP09.c_val]. intros i Hi. assert (i = 0) as -> by lia.
    destruct (aview_byte SEGS (w_H W) memc P VL HbP) as (b & Hb & Hv & _).
    exists b. split.
    * cbn [YP09.cbyte]. f_equal. unfold YP09.byte_of_word. cbn [sv_denot]. rewrite E35.
      rewrite !Z.add_0_r, (unsigned_lit_small VL), (unsigned_lit_small VL) by lia. change (8 * 0) with 0.
      rewrite Z.shiftr_0_r. subst VL. apply Z_to_bv_bv_unsigned.
    * rewrite !Z.add_0_r. exact Hb.
- unfold s3_rgB, s3_slot. cbn [YP09.pairwise_disjoint YP09.all_disjoint]. unfold YP09.extent_disjoint.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.base_val].
  rewrite E9, E25, E34, !unsigned_lit_small by lia. repeat split; lia.
- split; [|split; [exact I|]].
  + cbn [s3_fB f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite E22, E25, E10, E34, E33, E35, !unsigned_lit_small by (unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB. repeat split; lia.
  + cbn [s3_fB f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
    rewrite (U_atom _ 25 vp0 E25), (U_atom _ 10 nV E10), (U_atom_off _ 34 P 1 E34) by lia.
    rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Lemma s3_shokB : forall (W : world SEGS) (rX : bvmap 5 word) memc c V0 P VL vp0,
  getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF -> getr rX (Z_to_bv 5 25) = w64 vp0 ->
  0 <= vp0 < 2 ^ 64 -> 0 <= P < 2 ^ 64 ->
  range_addressable (rdW W memc) SHADOW_OFF vp0 1 -> range_addressable (rdW W memc) SHADOW_OFF P 1 ->
  ~ (SHADOW_OFF <= vp0 < SHADOW_OFF + 17592186044416) -> ~ (SHADOW_OFF <= P < SHADOW_OFF + 17592186044416) ->
  sh_ok SEGS s3_Bx s3_SHB (s3_EB rX c V0 P VL) (mrestrict (w_H W) memc).
Proof.
intros W rX memc c V0 P VL vp0 H22 H25 Hv HP R0 RP A0 AP.
assert (E22 : ew (s3_EB rX c V0 P VL) 22 = Z_to_bv 64 SHADOW_OFF)
  by (unfold s3_EB; rewrite (ew_Eimg_Ereg_nat rX _ 22 (Z_to_bv 5 22) eq_refl); exact H22).
assert (E25 : ew (s3_EB rX c V0 P VL) 25 = Z_to_bv 64 vp0)
  by (unfold s3_EB; rewrite (ew_Eimg_Ereg_nat rX _ 25 (Z_to_bv 5 25) eq_refl); exact H25).
assert (E34 : ew (s3_EB rX c V0 P VL) 34 = Z_to_bv 64 P)
  by (unfold s3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (UB : U (s3_EB rX c V0 P VL) s3_Bx = SHADOW_OFF)
  by (unfold s3_Bx; apply (U_atom _ 22 SHADOW_OFF E22); unfold SHADOW_OFF; lia).
assert (U25 : U (s3_EB rX c V0 P VL) (SOff 25 0) = vp0) by (apply (U_atom _ 25 vp0 E25); lia).
assert (U34 : U (s3_EB rX c V0 P VL) (SOff 34 0) = P) by (apply (U_atom _ 34 P E34); lia).
unfold sh_ok, s3_SHB. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (shent_ok_of_range SEGS (w_H W) memc _ s3_Bx 25%nat vp0 1 vp0 0 1 R0 UB U25); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  assert (y = vp0) as -> by lia. exact A0.
- apply (shent_ok_of_range SEGS (w_H W) memc _ s3_Bx 34%nat P 1 P 0 1 RP UB U34); [lia | lia |].
  intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy.
  assert (y = P) as -> by lia. exact AP.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---- K5 from K3 and what a run of the stretch leaves ---- *)
Ltac s3_old HK HRG :=
  lazymatch goal with |- getr _ (Z_to_bv 5 ?k) = _ =>
    rewrite (HK k ltac:(s3_inz));
    apply (a5_rg_get _ _ _ _ HRG); unfold A9_RC, PF_RM; cbn [In app]; repeat (first [left; reflexivity | right])
  end.

Lemma s3_fin : forall n x ei kp vp0 lyc Sc Wc rX memc mdc (rX' : bvmap 5 word) memc' mdc' P vp,
  INV_K3 B n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x))
    (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  vp0 <= P < a9_buf x + 512 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r S3_KEPT -> getr rX' r = getr rX r) ->
  getr rX' (Z_to_bv 5 24) = w64 (p_c (y_v x)) -> getr rX' (Z_to_bv 5 25) = w64 vp ->
  a9_inbuf (rdW Wc memc') x vp (a9_val x ei) ->
  INV_K5 B n x ei kp vp lyc Sc Wc rX' memc' mdc'.
Proof.
intros n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' P vp
  (HC & HCH & (HKS & HKB) & HSEP & (HVS & HVB) & HRG) HJ' HP KM KP HK R24 R25 HVAL'.
destruct HC as (HB & HM & HST & HSL & HLEN & HD0 & HDL).
pose proof (a5_geo _ _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & _ & _).
pose proof HB as (_ & _ & HOBJ & _ & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & HCB & _).
pose proof asan_consts as (AC1 & _).
unfold a9_buf, PF_O_BUF in HP. unfold pf_inb, a9_buf, PF_O_BUF in HKB, HVB.
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
assert (KW : forall sl shw a, 0 <= a < 2 ^ 64 -> ~ a5_Wrx (y_v x) (y_pos x) sl shw a ->
  rdW Wc memc' a = rdW Wc memc a).
{ intros sl shw a Ha Hn. apply KM; [exact Ha|]. intros ->. apply Hn. right. right. left. unfold a5_buf, PF_O_BUF. lia. }
assert (HK' : forall r, In r S3_KZ -> getr rX' (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r))
  by (intros r Hr; apply HK; apply in_map; exact Hr).
assert (HFI' : pf_rg rX' (a5_FI B (y_v x))).
{ apply (s3_rg_keep rX); [|exact (a5_fi_regs _ _ _ _ _ _ _ _ _ _ HB)].
  intros r Hr. apply HK'. unfold a5_FI in Hr. unfold S3_KZ. cbn [map fst In] in *. lia. }
assert (HB' : pf_base B (y_v x) (y_pos x) lyc Sc Wc rX' memc' mdc' PF_SC_LINE).
{ refine (a5_move0 B _ _ lyc Sc Wc rX memc mdc PF_SC_LINE Sc Wc rX' memc' mdc' PF_SC_LINE HB HJ' _
    (Permutation_refl _) (KW true true) KP HFI' _).
  - exists (st_fs Sc). destruct Sc; reflexivity.
  - exact (a5_keep_fsh _ _ _ _ true PF_SC_LINE G (KW true false) HFSH). }
split.
{ split; [exact HB'|]. split; [exact HM|].
  split; [exact (a5_keep_st B _ _ lyc Sc Wc memc mdc Wc memc' G HAR Hin Hly (KW true true) _ _ _ _ HCB HST)|].
  split; [exact (a5_keep_slot _ _ _ _ true _ G (KW false true) HSL)|].
  split; [exact HLEN|]. split; [exact HD0 | exact HDL]. }
split; [exact HCH|].
split.
{ split; [|unfold pf_inb, a9_buf, PF_O_BUF; lia]. apply (s3_str_keep _ _ _ _ HKS); [|exact KP].
  intros a Ha. apply KM; lia. }
split; [exact HVAL'|].
unfold pf_rg, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
- s3_old HK' HRG.
- s3_old HK' HRG.
- exact R24.
- s3_old HK' HRG.
- s3_old HK' HRG.
- s3_old HK' HRG.
- s3_old HK' HRG.
- s3_old HK' HRG.
- exact R25.
Qed.

Lemma s3_close : forall n, from_K5 B n -> forall x ei kp vp0 lyc Sc Wc rX memc mdc,
  INV_K3 B n x ei kp vp0 lyc Sc Wc rX memc mdc ->
  forall (rX' : bvmap 5 word) memc' mdc' P vp pc, pc = A9_K5 ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 (y_v x)) (seg_spec.RC_PARSE_W (p_c (y_v x))) (p_ly (y_v x))
    (p_S (y_v x)) (p_W (y_v x)) (p_mem (y_v x)) (p_md (y_v x)) [(5, y_pos x)] lyc Sc Wc memc' mdc' 0 ->
  vp0 <= P < a9_buf x + 512 ->
  (forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc memc' a = rdW Wc memc a) ->
  (forall a, rdW Wc memc a <> None -> rdW Wc memc' a <> None) ->
  (forall r, In r S3_KEPT -> getr rX' r = getr rX r) ->
  getr rX' (Z_to_bv 5 24) = w64 (p_c (y_v x)) -> getr rX' (Z_to_bv 5 25) = w64 vp ->
  a9_inbuf (rdW Wc memc') x vp (a9_val x ei) ->
  SRr SEGS Wc (mkCfg (mkst rX' (Z_to_bv 64 (BASE + pc)) memc' (seg_rom SEGS)) mdc') (a9_goal B x).
Proof.
intros n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI rX' memc' mdc' P vp pc -> HJ' HP KM KP HK R24 R25 HV.
exact (HK5 x ei kp vp lyc Sc Wc rX' memc' mdc'
  (s3_fin n x ei kp vp0 lyc Sc Wc rX memc mdc rX' memc' mdc' P vp HI HJ' HP KM KP HK R24 R25 HV)).
Qed.

(* the leaf of a run: the kept registers, s8 and s9, the cfg in mkst form *)
Ltac s3_leaf HS rX HA0 HAE HK N24 N25 :=
  pose proof (regs_kept_of_st_ok_pi _ _ _ rX _ S3_KEPT HS (s3_ag32 _ _ _ _ HA0 HAE) ltac:(vm_compute; reflexivity)) as HK;
  cbn [ms_regs restrict] in HK;
  s3_reg HS (Z_to_bv 5 24) N24; s3_reg HS (Z_to_bv 5 25) N25.

(* ---- |v| < 2: no strip ---- *)
Lemma s3_short : forall n, from_K5 B n -> forall x ei kp vp0 lyc Sc Wc rX memc mdc,
  INV_K3 B n x ei kp vp0 lyc Sc Wc rX memc mdc -> (length (a9_v0 x ei) < 2)%nat ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_K3) rX memc mdc) (a9_goal B x).
Proof.
intros n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI Hl.
pose proof HI as (HC & _ & _ & _ & (HVS & HVB) & HRG).
pose proof HC as (HB & _).
pose proof (a5_geo _ _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs _ _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & HFIx & _ & HSLB & _).
pose proof HFIx as (HJ & _).
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof asan_consts as (AC1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof HVS as ((HZS & NZ) & _).
unfold pf_inb, a9_buf, PF_O_BUF in HVB.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 (y_v x)))
  by (apply (a5_rg_get _ _ _ _ HFI); unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (apply (a5_rg_get _ _ _ _ HFI); unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (Z.of_nat (length (a9_v0 x ei))))
  by (apply (a5_rg_get _ _ _ _ HRG); unfold A9_RC, PF_RM; cbn [In app]; repeat (first [left; reflexivity | right])).
assert (Hslot : rdword (rdW Wc memc) (pf_s1 (y_v x) + 0x90) = Some (p_c (y_v x))).
{ pose proof (proj1 (Forall_forall _ _) HSLB (0x90, p_c (y_v x))) as H. cbn [fst snd] in H. apply H.
  unfold PF_SL. cbn [In]. repeat (first [left; reflexivity | right]). }
pose proof (s3_entryA Wc rX memc (pf_s1 (y_v x)) (Z.of_nat (length (a9_v0 x ei))) (p_c (y_v x)) R9 R22 R10
  ltac:(lia) ltac:(lia) Hc64 ltac:(lia) Hslot) as HS.
assert (HEI : img_env VAL A_LIM (s3_EA rX (p_c (y_v x)))) by (unfold s3_EA; apply Eimg_env).
assert (SHOK : sh_ok SEGS s3_Bx [] (s3_EA rX (p_c (y_v x))) (mrestrict (w_H Wc) memc)) by constructor.
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (p_c (y_v x))]) (s3_EA rX (p_c (y_v x))))
  by (split; [intros k Hk; unfold s3_EA; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E32 : ew (s3_EA rX (p_c (y_v x))) 32 = Z_to_bv 64 (p_c (y_v x)))
  by (unfold s3_EA; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E25 : ew (s3_EA rX (p_c (y_v x))) 25 = Z_to_bv 64 vp0).
{ unfold s3_EA. rewrite (ew_Eimg_Ereg_nat rX _ 25 (Z_to_bv 5 25) eq_refl).
  apply (a5_rg_get _ _ _ _ HRG). unfold A9_RC, PF_RM. cbn [In app]. repeat (first [left; reflexivity | right]). }
revert HS HEI SHOK HA0 E32 E25. generalize (s3_EA rX (p_c (y_v x))) as E0. intros E0 HS HEI SHOK HA0 E32 E25.
pose proof (env_agree_refl 36 E0) as HAE.
unfold cfg_at. change (w64 (BASE + A9_K3)) with (Z_to_bv 64 (BASE + A9_K3)).
(* 0x87ff4 .. 0x8814c: bltu decided (|v| < 2), ld s8, 0x90(s1), j K5 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K5.
{ lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
set (mdv := with_vm_backing _ _ _) in *; clearbody mdv.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. rewrite (kept_of_frame (segs := SEGS) _ _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr);
    [reflexivity | s3_win | exact Ha | tauto]. }
assert (KP : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Ha; exact (s3_view_grows _ _ _ a HG Ha)).
lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
  assert (HAE' : env_agree 36 E0 En) by (env_agree_chain HAE) end.
s3_leaf HS rX HA0 HAE' HK N24 N25.
rewrite (s3_den_off _ 32 (p_c (y_v x)) 0 (s3_ag_ew _ _ 32 _ HAE' ltac:(lia) E32) Hc64), Z.add_0_r in N24.
rewrite (s3_den_off _ 25 vp0 0 (s3_ag_ew _ _ 25 _ HAE' ltac:(lia) E25) ltac:(lia)), Z.add_0_r in N25.
pmkst HS.
apply (s3_close n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI _ _ _ vp0 vp0 _ eq_refl HJ);
  [unfold a9_buf, PF_O_BUF; lia | intros a Ha _; exact (KM a Ha) | exact KP | exact HK | exact N24 | exact N25 |].
unfold a9_val. rewrite (a9_unq_short _ NZ Hl). split; [|unfold pf_inb, a9_buf, PF_O_BUF; lia].
apply (s3_str_keep _ _ _ _ HVS); [|exact KP].
intros a Ha. apply KM. lia.
Qed.

(* ---- |v| >= 2: the quote tests and the strip ---- *)
(* the run's writes: only the byte P of the last region (atom 34), inside the class-5 frame (awr_byte's own-frame
   case) *)
Ltac s3_awrB x Hly HAE E34 P :=
  lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  apply awr_ok_cons_ro; [cbn; lia|]; apply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_gen with (n := 34%nat) (b := P);
  [ reflexivity
  | rewrite (s3_ag_ew _ _ 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia
  | let a := fresh "a" in let Ha := fresh "Ha" in
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha;
    right; right; right; left; exists 5, (y_pos x); split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd];
    rewrite Hly; change (frame_addr (p_ly (y_v x)) 5 (y_pos x)) with (pf_F (y_v x) (y_pos x));
    change (fs_frame_bytes 5) with 2048; lia
  | apply awr_ok_nil ].
(* after a run: the environment agrees with the seed's below 36 (HAE), the memory is memc off P (KM), every
   mapped byte stays mapped (KP) *)
Ltac s3_after W memc E0 P E34 HAE KM KP :=
  let mdv := fresh "mdv" in
  set (mdv := with_vm_backing _ _ _) in *; clearbody mdv;
  lazymatch goal with
  | HS : st_ok_pi _ _ ?En _ (restrict _ ?msn), HFr : frame_of ?Eo ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)),
    HG : mem_grows (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msn)) |- _ =>
    let U := fresh "U" in
    assert (U : bv_unsigned (ew Eo 34) = P)
      by (rewrite (s3_ag_ew _ _ 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia);
    let HAEn := fresh "HAEn" in let KMn := fresh "KMn" in let KPn := fresh "KPn" in
    assert (HAEn : env_agree 36 E0 En) by (env_agree_chain HAE);
    assert (KMn : forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW W (ms_mem msn) a = rdW W memc a)
      by (apply (s3_keep_step Eo rs (w_H W) m0 (ms_mem msn) memc P HFr); [s3_win | exact KM]);
    assert (KPn : forall a, rdW W memc a <> None -> rdW W (ms_mem msn) a <> None)
      by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; exact (s3_view_grows _ _ _ a HG (KP a Ha)));
    clear U HFr HG HAE KM KP; rename HAEn into HAE; rename KMn into KM; rename KPn into KP
  end.
(* a leaf at K5 that made no store: a9_val = v, the value at vp0 unchanged *)
Ltac s3_keep_leaf n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI HS HJ HA0 HAE KM KP E32 E25 E34 E35 Hc64 P VL HbP
  NZ Hl HVS HV0 HVL :=
  let HK := fresh "HK" in let N24 := fresh "N24" in let N25 := fresh "N25" in let HWB := fresh "HWB" in
  s3_leaf HS rX HA0 HAE HK N24 N25;
  rewrite (s3_den_off _ 32 (p_c (y_v x)) 0 (s3_ag_ew _ _ 32 _ HAE ltac:(lia) E32) Hc64), Z.add_0_r in N24;
  rewrite (s3_den_off _ 25 vp0 0 (s3_ag_ew _ _ 25 _ HAE ltac:(lia) E25) ltac:(lia)), Z.add_0_r in N25;
  lazymatch type of HS with st_ok_pi _ _ ?En _ _ =>
    pose proof (s3_wbyte _ _ _ _ 34%nat 2%nat P (SOff 35 0) HS ltac:(vm_compute; reflexivity)
      ltac:(rewrite (s3_ag_ew _ _ 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia)) as HWB;
    rewrite (s3_byte_atom En 35 VL (s3_ag_ew _ _ 35 _ HAE ltac:(lia) E35) ltac:(lia)) in HWB end;
  pmkst HS;
  apply (s3_close n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI _ _ _ P vp0 _ eq_refl HJ);
  [ unfold a9_buf, PF_O_BUF; lia | exact KM | exact KP | exact HK | exact N24 | exact N25 |];
  unfold a9_val; rewrite (a9_unq_keep _ NZ Hl ltac:(rewrite HV0, HVL; lia));
  split; [|unfold pf_inb, a9_buf, PF_O_BUF; lia];
  apply (s3_str_keep _ _ _ _ HVS); [|exact KP];
  let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in intros a Ha;
  destruct (Z.eq_dec a P) as [-> | Hne]; [rewrite HWB, HbP; reflexivity | apply KM; [lia | exact Hne]].
(* a leaf at K5 after the strip store: a9_val = slice 1 (|v| - 1) v at vp0 + 1 *)
Ltac s3_strip_leaf q n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI HS HJ HA0 HAE KM KP E32 E25 E34 Hc64 P
  NZ Hl HVS HV0 HVL :=
  let HK := fresh "HK" in let N24 := fresh "N24" in let N25 := fresh "N25" in let HWB := fresh "HWB" in
  let HW0 := fresh "HW0" in
  s3_leaf HS rX HA0 HAE HK N24 N25;
  rewrite (s3_den_off _ 32 (p_c (y_v x)) 0 (s3_ag_ew _ _ 32 _ HAE ltac:(lia) E32) Hc64), Z.add_0_r in N24;
  rewrite (s3_den_off _ 25 vp0 1 (s3_ag_ew _ _ 25 _ HAE ltac:(lia) E25) ltac:(lia)) in N25;
  pose proof (s3_wbyte _ _ _ _ 34%nat 2%nat P (SLit 0) HS ltac:(vm_compute; reflexivity)
    ltac:(rewrite (s3_ag_ew _ _ 34 _ HAE ltac:(lia) E34); apply unsigned_lit_small; lia)) as HWB;
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msn) =>
    assert (HW0 : rdW Wc (ms_mem msn) P = Some 0) by (rewrite HWB; reflexivity) end;
  pmkst HS;
  apply (s3_close n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI _ _ _ P (vp0 + 1) _ eq_refl HJ);
  [ unfold a9_buf, PF_O_BUF; lia | exact KM | exact KP | exact HK | exact N24 | exact N25 |];
  unfold a9_val; rewrite (a9_unq_strip _ q NZ Hl ltac:(lia) ltac:(rewrite HV0; lia) ltac:(rewrite HVL; lia));
  split;
  [ apply (s3_str_strip _ _ _ _ P HVS Hl ltac:(lia)); [| exact HW0 | exact KP];
    let a := fresh "a" in let Ha := fresh "Ha" in let Hne := fresh "Hne" in
    intros a Ha Hne; apply KM; [lia | exact Hne]
  | unfold pf_inb, a9_buf, PF_O_BUF, slice; rewrite length_firstn, length_skipn; lia ].

Lemma s3_long : forall n, from_K5 B n -> forall x ei kp vp0 lyc Sc Wc rX memc mdc,
  INV_K3 B n x ei kp vp0 lyc Sc Wc rX memc mdc -> (2 <= length (a9_v0 x ei))%nat ->
  SRr SEGS Wc (cfg_at SEGS (BASE + A9_K3) rX memc mdc) (a9_goal B x).
Proof.
intros n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI Hl.
pose proof HI as (HC & _ & _ & _ & (HVS & HVB) & HRG).
pose proof HC as (HB & _).
pose proof (a5_geo _ _ _ _ _ _ _ _ _ _ HB) as (HAR & Hly & Hin & G & HFP & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12).
pose proof (a5_fi_regs _ _ _ _ _ _ _ _ _ _ HB) as HFI.
pose proof HB as (HCX & HFIx & _ & HSLB & HFSH).
pose proof HFIx as (HJ & _).
pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof asan_consts as (AC1 & _).
pose proof STK_values as (_ & _ & _ & SPF & _). rewrite SPF in G1.
pose proof HVS as ((HZS & NZ) & _).
unfold pf_inb, a9_buf, PF_O_BUF in HVB.
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 (y_v x)))
  by (apply (a5_rg_get _ _ _ _ HFI); unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R22 : getr rX (Z_to_bv 5 22) = w64 SHADOW_OFF)
  by (apply (a5_rg_get _ _ _ _ HFI); unfold a5_FI; cbn [In]; repeat (first [left; reflexivity | right])).
assert (R10 : getr rX (Z_to_bv 5 10) = w64 (Z.of_nat (length (a9_v0 x ei))))
  by (apply (a5_rg_get _ _ _ _ HRG); unfold A9_RC, PF_RM; cbn [In app]; repeat (first [left; reflexivity | right])).
assert (R25 : getr rX (Z_to_bv 5 25) = w64 vp0)
  by (apply (a5_rg_get _ _ _ _ HRG); unfold A9_RC, PF_RM; cbn [In app]; repeat (first [left; reflexivity | right])).
assert (Hslot : rdword (rdW Wc memc) (pf_s1 (y_v x) + 0x90) = Some (p_c (y_v x))).
{ pose proof (proj1 (Forall_forall _ _) HSLB (0x90, p_c (y_v x))) as H. cbn [fst snd] in H. apply H.
  unfold PF_SL. cbn [In]. repeat (first [left; reflexivity | right]). }
destruct (s3_ex (nth 0 (a9_v0 x ei) 0)) as (V0 & HV0).
destruct (s3_ex (nth (length (a9_v0 x ei) - 1) (a9_v0 x ei) 0)) as (VL & HVL).
destruct (s3_ex (vp0 + Z.of_nat (length (a9_v0 x ei)) - 1)) as (P & HPd).
assert (Hb0 : rdW Wc memc vp0 = Some V0).
{ rewrite <- HV0. pose proof (s3_zs_nth _ _ _ 0 HZS ltac:(lia)) as Z0. rewrite Z.add_0_r in Z0. exact Z0. }
assert (HbP : rdW Wc memc P = Some VL).
{ rewrite <- HVL. pose proof (s3_zs_nth _ _ _ (length (a9_v0 x ei) - 1) HZS ltac:(lia)) as ZL.
  replace (vp0 + Z.of_nat (length (a9_v0 x ei) - 1)) with P in ZL by lia. exact ZL. }
destruct (aview_byte SEGS (w_H Wc) memc vp0 V0 Hb0) as (_ & _ & _ & RV0).
destruct (aview_byte SEGS (w_H Wc) memc P VL HbP) as (_ & _ & _ & RVL).
assert (HpP : apresent (w_H Wc) memc P) by (apply HFP; lia).
assert (AP : forall y, pf_F (y_v x) (y_pos x) <= y < pf_F (y_v x) (y_pos x) + 2048 ->
  ~ (SHADOW_OFF <= y < SHADOW_OFF + 17592186044416)).
{ intros y Hy. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in G9. unfold SHADOW_OFF. lia. }
pose proof (a9_buf_addr (rdW Wc memc) (pf_SH (y_v x) (y_pos x)) (pf_F (y_v x) (y_pos x)) vp0 1 HFSH eq_refl
  (s3_mod8 _ G8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RA0.
pose proof (a9_buf_addr (rdW Wc memc) (pf_SH (y_v x) (y_pos x)) (pf_F (y_v x) (y_pos x)) P 1 HFSH eq_refl
  (s3_mod8 _ G8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as RAP.
pose proof (s3_entryB Wc rX memc (pf_s1 (y_v x)) vp0 (Z.of_nat (length (a9_v0 x ei))) (p_c (y_v x)) V0 P VL
  R9 R22 R25 R10 ltac:(lia) ltac:(lia) Hc64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) Hslot Hb0 HbP HpP) as HS.
pose proof (s3_shokB Wc rX memc (p_c (y_v x)) V0 P VL vp0 R22 R25 ltac:(lia) ltac:(lia) RA0 RAP
  (AP vp0 ltac:(lia)) (AP P ltac:(lia))) as SHOK.
assert (HEI : img_env VAL A_LIM (s3_EB rX (p_c (y_v x)) V0 P VL)) by (unfold s3_EB; apply Eimg_env).
assert (HA0 : env_agree 32 (Ereg rX [Z_to_bv 64 (p_c (y_v x)); Z_to_bv 64 V0; Z_to_bv 64 P; Z_to_bv 64 VL])
  (s3_EB rX (p_c (y_v x)) V0 P VL))
  by (split; [intros k Hk; unfold s3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (E32 : ew (s3_EB rX (p_c (y_v x)) V0 P VL) 32 = Z_to_bv 64 (p_c (y_v x)))
  by (unfold s3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew (s3_EB rX (p_c (y_v x)) V0 P VL) 33 = Z_to_bv 64 V0)
  by (unfold s3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew (s3_EB rX (p_c (y_v x)) V0 P VL) 34 = Z_to_bv 64 P)
  by (unfold s3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (E35 : ew (s3_EB rX (p_c (y_v x)) V0 P VL) 35 = Z_to_bv 64 VL)
  by (unfold s3_EB; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 3)).
assert (E25 : ew (s3_EB rX (p_c (y_v x)) V0 P VL) 25 = Z_to_bv 64 vp0)
  by (unfold s3_EB; rewrite (ew_Eimg_Ereg_nat rX _ 25 (Z_to_bv 5 25) eq_refl); exact R25).
revert HS HEI SHOK HA0 E32 E33 E34 E35 E25.
generalize (s3_EB rX (p_c (y_v x)) V0 P VL) as E0. intros E0 HS HEI SHOK HA0 E32 E33 E34 E35 E25.
pose proof (env_agree_refl 36 E0) as HAE.
assert (KM : forall a, 0 <= a < 2 ^ 64 -> a <> P -> rdW Wc memc a = rdW Wc memc a) by (intros; reflexivity).
assert (KP : forall a, rdW Wc memc a <> None -> rdW Wc memc a <> None) by (intros a Ha; exact Ha).
unfold cfg_at. change (w64 (BASE + A9_K3)) with (Z_to_bv 64 (BASE + A9_K3)).
(* 0x87ff4 .. 0x88018: bltu decided (|v| >= 2), check 10, ld s8, 0x90(s1), lbu V[0], beq SQ *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ s3_awrB x Hly HAE E34 P. }
s3_after Wc memc E0 P E34 HAE KM KP.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* V[0] = SQ: 0x88108 check 14, lbu V[|v| - 1], bne SQ *)
  pose proof (s3_br_eq _ 33 _ 39 _ (s3_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C0.
  apply Z.eqb_eq in C0. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { s3_awrB x Hly HAE E34 P. }
  s3_after Wc memc E0 P E34 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* V[|v| - 1] <> SQ: no strip, K5 *)
    pose proof (s3_br_ne _ 35 _ 39 _ (s3_ag_ew _ _ 35 _ HAE ltac:(lia) E35) ltac:(lia) ltac:(lia) Hc) as C1.
    apply Bool.negb_true_iff in C1. apply Z.eqb_neq in C1. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K5.
    { s3_awrB x Hly HAE E34 P. }
    s3_after Wc memc E0 P E34 HAE KM KP.
    s3_keep_leaf n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI HS HJ HA0 HAE KM KP E32 E25 E34 E35 Hc64 P VL HbP NZ Hl HVS HV0 HVL.
  + (* V[|v| - 1] = SQ: check 15, the NUL store, s9 = vp0 + 1, K5 *)
    pose proof (s3_br_ne _ 35 _ 39 _ (s3_ag_ew _ _ 35 _ HAE ltac:(lia) E35) ltac:(lia) ltac:(lia) Hc) as C1.
    apply Bool.negb_false_iff in C1. apply Z.eqb_eq in C1. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K5.
    { s3_awrB x Hly HAE E34 P. }
    s3_after Wc memc E0 P E34 HAE KM KP.
    s3_strip_leaf 39 n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI HS HJ HA0 HAE KM KP E32 E25 E34 Hc64 P NZ Hl HVS HV0 HVL.
- (* V[0] <> SQ: bne DQ *)
  pose proof (s3_br_eq _ 33 _ 39 _ (s3_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C0.
  apply Z.eqb_neq in C0. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { s3_awrB x Hly HAE E34 P. }
  s3_after Wc memc E0 P E34 HAE KM KP.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* V[0] <> DQ: no strip, K5 *)
    pose proof (s3_br_ne _ 33 _ 34 _ (s3_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C1.
    apply Bool.negb_true_iff in C1. apply Z.eqb_neq in C1. clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K5.
    { s3_awrB x Hly HAE E34 P. }
    s3_after Wc memc E0 P E34 HAE KM KP.
    s3_keep_leaf n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI HS HJ HA0 HAE KM KP E32 E25 E34 E35 Hc64 P VL HbP NZ Hl HVS HV0 HVL.
  + (* V[0] = DQ: check 11, lbu V[|v| - 1], beq DQ *)
    pose proof (s3_br_ne _ 33 _ 34 _ (s3_ag_ew _ _ 33 _ HAE ltac:(lia) E33) ltac:(lia) ltac:(lia) Hc) as C1.
    apply Bool.negb_false_iff in C1. apply Z.eqb_eq in C1. clear Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { s3_awrB x Hly HAE E34 P. }
    s3_after Wc memc E0 P E34 HAE KM KP.
    psrr_branch_tok RUN BR HS SHOK Bspan.
    * (* V[|v| - 1] = DQ: check 15, the NUL store, K5 *)
      pose proof (s3_br_eq _ 35 _ 34 _ (s3_ag_ew _ _ 35 _ HAE ltac:(lia) E35) ltac:(lia) ltac:(lia) Hc) as C2.
      apply Z.eqb_eq in C2. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K5.
      { s3_awrB x Hly HAE E34 P. }
      s3_after Wc memc E0 P E34 HAE KM KP.
      s3_strip_leaf 34 n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI HS HJ HA0 HAE KM KP E32 E25 E34 Hc64 P NZ Hl HVS HV0 HVL.
    * (* V[|v| - 1] <> DQ: no strip, K5 *)
      pose proof (s3_br_eq _ 35 _ 34 _ (s3_ag_ew _ _ 35 _ HAE ltac:(lia) E35) ltac:(lia) ltac:(lia) Hc) as C2.
      apply Z.eqb_neq in C2. clear Hc.
      paj_run_to_tok RUNTO HS HJ SHOK Bspan A9_K5.
      { s3_awrB x Hly HAE E34 P. }
      s3_after Wc memc E0 P E34 HAE KM KP.
      s3_keep_leaf n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI HS HJ HA0 HAE KM KP E32 E25 E34 E35 Hc64 P VL HbP NZ Hl HVS HV0 HVL.
Qed.

(** ** The stretch: K3 -> K5 *)
Lemma a9_sC : SA9_C B.
Proof.
unfold SA9_C. intros n HK5. unfold from_K3, a9_from. intros x ei kp vp0 lyc Sc Wc rX memc mdc HI.
destruct (Nat.lt_ge_cases (length (a9_v0 x ei)) 2) as [Hs | Hl].
- exact (s3_short n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI Hs).
- exact (s3_long n HK5 x ei kp vp0 lyc Sc Wc rX memc mdc HI Hl).
Qed.

End e.
End f.
End d.
