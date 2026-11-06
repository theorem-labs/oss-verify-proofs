(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the helpers of pins_clear's ASan+UBSan walk (plugin-hostd/fuzz_command, image
   fuzz_command.asan-ubsan; the walk is lib/B/Prog/pins_clear.v): the listing of the function, the entry state and
   g_rec's region, the model's two arms, the refusal word's sign extension and the test, the recorder's
   representation after the store of g_rec.state, the call targets, and the footprint and journal facts. Copied in
   part from the ASan walk (lib/A/Prog/pins_clear_s4.v on a working branch 3cc8391594b) and from the B helper
   files of descriptors_add (a working branch 92b1730d737) and lv2_refusals_forget
   (a working branch 6a72ccf993e), re-derived on pins_clear's B code.

   B's code (fuzz_command.asan-ubsan sha256 658cefbe806b535ba1fbe5a37c8efe02099fc39c326f300e9b1c969d479df401,
   .symtab pins_clear = 0x8cbe8, size 108 = 27 instructions, all 4 bytes; listing lib/B/Prog/CmdList.v:6653-6679;
   entry BASE + AF_pins_clear):
     0x8cbe8 .. 0x8cbfc  the 32-byte frame (ra at sp0 - 8, s0 at sp0 - 16, s1 at sp0 - 24), s1 := uri, a0 := 21
     0x8cc00             jal record                      (returns the slot c in a0)
     0x8cc04 .. 0x8cc08  s0 := c, a1 := uri
     0x8cc0c             jal arg_s
     0x8cc10 .. 0x8cc18  s1 := g_rec (auipc a0 = A_HI 202, addi s1 = A_OBJ 44), a0 := g_rec.refuse (lw, sign-extended)
     0x8cc1c             beqz a0, 0x8cc28                 the refusal test (the only conditional branch)
     0x8cc20 .. 0x8cc24  refused: a0 := g_rec.code (lw 4(s1)), j 0x8cc40
     0x8cc28 .. 0x8cc2c  not refused: a0 := g_rec.state (ld 0x3b0(s1)), a1 := c
     0x8cc30             jal mix_call                    (returns the digest in a0)
     0x8cc34 .. 0x8cc3c  a1 := digest, a0 := 0 (SUCCESS), g_rec.state := a1 (sd a1,0x3b0(s1))
     0x8cc40 .. 0x8cc4c  ra / s0 / s1 reloaded, the frame popped
     0x8cc50             j answer_code                   (tail jump at the entry sp)
   No `jal __asan_report_*` and no unimp / ebreak in [0x8cbe8, 0x8cc54): 0 report edges and 0 UBSan trap edges. Every
   g_rec access goes through s1 = the object atom A_OBJ 44 (cmd_val_objs), never through an auipc (A_HI) base, so
   the walk needs no `cmd_val_his`. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdAddr CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import
PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot PaNoChain.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import RecBLemmas.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* --- the listing ------------------------------------------------------------------------------------------- *)
(* the listing offsets of the walk's stops (BASE + AF_pins_clear = 0x8cbe8) *)
Definition P_REC_RET : Z := AF_pins_clear + 0x1c.  (* 0x8cc04, after jal record *)
Definition P_ARG_RET : Z := AF_pins_clear + 0x28.  (* 0x8cc10, after jal arg_s *)
Definition P_REFBR : Z := AF_pins_clear + 0x34.    (* 0x8cc1c, beqz a0 (g_rec.refuse) *)
Definition P_REFUSE : Z := AF_pins_clear + 0x38.   (* 0x8cc20, refused: lw a0,4(s1) *)
Definition P_ZERO : Z := AF_pins_clear + 0x40.     (* 0x8cc28, not refused: ld a0,0x3b0(s1) *)
Definition P_MIX_RET : Z := AF_pins_clear + 0x4c.  (* 0x8cc34, after jal mix_call *)
Definition P_EPI : Z := AF_pins_clear + 0x58.      (* 0x8cc40, both arms meet: the epilogue *)
Definition P_TAIL : Z := AF_pins_clear + 0x68.     (* 0x8cc50, j answer_code *)

Lemma pcb_pcs :
cmd_text + AF_pins_clear = 0x8cbe8 /\ cmd_text + P_REC_RET = 0x8cc04 /\ cmd_text + P_ARG_RET = 0x8cc10 /\
cmd_text + P_REFBR = 0x8cc1c /\ cmd_text + P_REFUSE = 0x8cc20 /\ cmd_text + P_ZERO = 0x8cc28 /\
cmd_text + P_MIX_RET = 0x8cc34 /\ cmd_text + P_EPI = 0x8cc40 /\ cmd_text + P_TAIL = 0x8cc50.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* the 27 slots from the entry: the listing names the three calls, the tail jump, and the auipc/addi pair that
   gives s1 = g_rec (A_HI 202, A_OBJ 44); the loads and the store of g_rec's words are plain words through s1 *)
Lemma pcb_listing : firstn 27 (skipn (Z.to_nat (AF_pins_clear / 4)) cmd_listing) =
[PW 0xfe010113; PW 0x113c23; PW 0x813823; PW 0x913423; PW 0x50493; PW 0x1500513; PCall CS_record (1%bv : bv 5);
 PW 0x50413; PW 0x48593; PCall CS_arg_s (1%bv : bv 5); PHi (10%bv : bv 5) 202;
 PAddHi (9%bv : bv 5) (10%bv : bv 5) 202 (A_OBJ 44) 0x0; PW 0x4a503; PW 0x50663; PW 0x44a503; PW 0x1c0006f;
 PW 0x3b04b503; PW 0x40593; PCall CS_mix_call (1%bv : bv 5); PW 0x50593; PW 0x513; PW 0x3ab4b823;
 PW 0x1813083; PW 0x1013403; PW 0x813483; PW 0x2010113; PTail CS_answer_code].
Proof. vm_compute. reflexivity. Qed.

(* the image's addresses behind the listing's names: the callees' offsets, g_rec (object 44), record.spill
   (object 53) and the auipc value 0x5e2c10 (hi 202), 0x6b0 below g_rec *)
Lemma pcb_addrs :
cmd_af CS_pins_clear = AF_pins_clear /\ cmd_af CS_record = AF_record /\ cmd_af CS_arg_s = AF_arg_s /\
cmd_af CS_mix_call = AF_mix_call /\ cmd_af CS_answer_code = AF_answer_code /\
(44 < length cmd_objs)%nat /\ cmd_obj 44 = A_G_REC /\ (53 < length cmd_objs)%nat /\ cmd_obj 53 = A_REC_SPILL /\
(202 < length cmd_his)%nat /\ cmd_hi 202 = A_G_REC - 0x6b0.
Proof. vm_compute. repeat split; first [reflexivity | lia]. Qed.

(* the four callees are program functions of the listing *)
Lemma pcb_prog_syms : In CS_record cmd_prog_syms /\ In CS_arg_s cmd_prog_syms /\
In CS_mix_call cmd_prog_syms /\ In CS_answer_code cmd_prog_syms.
Proof. vm_compute. repeat split; repeat (first [left; reflexivity | right]). Qed.

(* the footprint the statement gives (pins_clear_c.v, apost_baseF's region list); the program's own writable statics
   as as_prog_static lists them (base, length) are a Theorem Labs lane's TFIB_PROG_STATIC (lib/B/YF0m.v) *)
Definition pcb_FP (O : list (Z * Z)) : list (Z * Z) :=
(A_G_REC, A_G_REC + REC_SIZE) :: (A_REC_SPILL, A_REC_SPILL + SC_SIZE) :: ablocks_fp O.

(* --- the symbolic states ----------------------------------------------------------------------------------- *)
(* atom 2 (sp) is 16-aligned and in the stack window *)
Definition pcb_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].
(* the entry: every register its own atom, the 32 bytes below sp writable *)
Definition pcb_ss0 : sstate := mkSS AF_pins_clear sr_atoms [stack_region 32] None pcb_facts.
(* g_rec after the call of arg_s, as the code reads and writes it through s1 = g_rec (the listing's object 44):
   refuse (+0) and code (+4) as unsigned 32-bit words (atoms 32, 33: the entry environment's extra atoms), state
   (+944, atom 34); the store at 0x8cc3c writes state *)
Definition pcb_grec : YP09.region :=
YP09.mkRegion (Some (A_OBJ 44)) 0 952 944 952
  [YP09.mkChunk 0 (CVal 4 (SOff 32 0)); YP09.mkChunk 4 (CVal 4 (SOff 33 0)); YP09.mkChunk 944 (CVal 8 (SOff 34 0))].

(* --- the model --------------------------------------------------------------------------------------------- *)
Lemma pcb_rr_fields : forall R fn A,
r_refuse (rec_record R fn A) = r_refuse R /\ r_code (rec_record R fn A) = r_code R /\
r_state (rec_record R fn A) = r_state R.
Proof.
intros R fn A. unfold rec_record. destruct (Nat.ltb (length (r_calls R)) 16); destruct R; cbn; repeat split.
Qed.
Lemma pcb_rr_set_state : forall R h fn A, rec_record (set_state R h) fn A = set_state (rec_record R fn A) h.
Proof.
intros R h fn A. unfold rec_record. change (r_calls (set_state R h)) with (r_calls R).
destruct (Nat.ltb (length (r_calls R)) 16); destruct R; reflexivity.
Qed.
Lemma pcb_set_state_id : forall R, set_state R (r_state R) = R.
Proof. intros R. destruct R. reflexivity. Qed.
(* the call's model on the two arms of the refusal test (RecModel.v:77-79, 92-93): record(21) of the argument,
   then either g_rec.state := mix_call(state, the call) and the code 0, or the input's refusal code; answer_code
   keeps the code's text as the answer. h is g_rec.state at the tail jump, code is a0 there. *)
Lemma pcb_model : forall R u h code,
(r_refuse R = 0 /\ h = mixcall (r_state R) REC_PINS_CLEAR [u] /\ code = 0) \/
(r_refuse R <> 0 /\ h = r_state R /\ code = r_code R) ->
pins_clear_m R (Some u) = rec_answer_code (rec_record (set_state R h) REC_PINS_CLEAR [u]) code.
Proof.
intros R u h code HMOD. unfold pins_clear_m, rec_stub_code. cbv zeta. cbn [sarg].
destruct (pcb_rr_fields R REC_PINS_CLEAR [u]) as (Fr & Fc & Fs). rewrite Fr.
destruct HMOD as [(HR0 & -> & ->) | (HR0 & -> & ->)].
- rewrite HR0. cbn [Z.eqb]. rewrite pcb_rr_set_state. unfold rec_mix. cbn [fst snd]. rewrite Fs. reflexivity.
- replace (r_refuse R =? 0) with false by (symmetry; apply Z.eqb_neq; exact HR0).
  rewrite pcb_set_state_id, Fc. reflexivity.
Qed.

(* --- the refusal word and the code: 32-bit words of g_rec, loaded with sign extension (lw) ------------------- *)
Lemma pcb_aval_mod : forall rd a v, aval_mem rd a 4 v -> aval_mem rd a 4 (v mod 2 ^ 32).
Proof.
intros rd a v H k Hk. rewrite (H k Hk). f_equal. unfold YG0f.le_byte. change (8 * Z.of_nat 4) with 32.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma pcb_sext32 : forall E n v, ew E n = Z_to_bv 64 (v mod 2 ^ 32) -> -2 ^ 31 <= v < 2 ^ 31 ->
U E (SExt true 32 (SOff n 0)) = v mod 2 ^ 64.
Proof.
intros E n v Hn Hv. rewrite U_SExt. cbv beta iota.
pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)) as Hm.
rewrite (U_atom E n (v mod 2 ^ 32) Hn ltac:(lia)).
change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite Z.mod_mod by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
rewrite Zplus_mod_idemp_l. rewrite (Z.mod_small (v + 2 ^ 31)) by lia.
replace (v + 2 ^ 31 - 2 ^ 31) with v by lia.
rewrite zcanon_wrap. unfold bv_wrap. reflexivity.
Qed.
Lemma pcb_sext32_denot : forall E n v, ew E n = Z_to_bv 64 (v mod 2 ^ 32) -> -2 ^ 31 <= v < 2 ^ 31 ->
sv_denot E (SExt true 32 (SOff n 0)) = Z_to_bv 64 v.
Proof.
intros E n v Hn Hv. apply bv_eq. rewrite Z_to_bv_unsigned.
change (bv_unsigned (sv_denot E (SExt true 32 (SOff n 0)))) with (U E (SExt true 32 (SOff n 0))).
rewrite (pcb_sext32 E n v Hn Hv). unfold bv_wrap. reflexivity.
Qed.
Lemma pcb_mod0 : forall v, -2 ^ 63 <= v < 2 ^ 63 -> v mod 2 ^ 64 = 0 -> v = 0.
Proof.
intros v Hv H. destruct (Z_lt_le_dec v 0) as [Hn | Hn].
- rewrite <- (Z.mod_add v 1 (2 ^ 64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
- rewrite Z.mod_small in H by lia. exact H.
Qed.
(* the refusal test at 0x8cc1c decides g_rec.refuse (atom n, its unsigned 32-bit word): taken iff it is 0 *)
Lemma pcb_br_zero : forall E n rf, ew E n = Z_to_bv 64 (rf mod 2 ^ 32) -> -2 ^ 31 <= rf < 2 ^ 31 ->
branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 0)) = true -> rf = 0.
Proof.
intros E n rf Hn Hrf Hc.
rewrite branch_eq_U, (pcb_sext32 E n rf Hn Hrf), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
apply Z.eqb_eq in Hc. apply pcb_mod0; [lia | exact Hc].
Qed.
Lemma pcb_br_refused : forall E n rf, ew E n = Z_to_bv 64 (rf mod 2 ^ 32) -> -2 ^ 31 <= rf < 2 ^ 31 ->
branch_taken BC_EQ (sv_denot E (SExt true 32 (SOff n 0))) (sv_denot E (SLit 0)) = false -> rf <> 0.
Proof.
intros E n rf Hn Hrf Hc ->.
rewrite branch_eq_U, (pcb_sext32 E n 0 Hn Hrf), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
vm_compute in Hc. discriminate Hc.
Qed.

(* --- the representation after the store of g_rec.state ---------------------------------------------------- *)
Lemma pcb_aval_mem_kept : forall (rd rd' : reader) a n v, aval_mem rd a n v ->
(forall k, (k < n)%nat -> rd' (a + Z.of_nat k) = rd (a + Z.of_nat k)) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v H Hk k Hkn. rewrite (Hk k Hkn). exact (H k Hkn). Qed.
Lemma pcb_rabytes_kept : forall (rd rd' : reader) a l, abytes_atR rd a l ->
(forall i, 0 <= i < Z.of_nat (length l) -> rd' (a + i) = rd (a + i)) -> abytes_atR rd' a l.
Proof. intros rd rd' a l H Hk i Hi. rewrite (Hk (Z.of_nat i) ltac:(lia)). exact (H i Hi). Qed.
Lemma pcb_rastr_kept : forall (rd rd' : reader) a s, astr_atR rd a s ->
(forall i, 0 <= i < Z.of_nat (length s) + 1 -> rd' (a + i) = rd (a + i)) -> astr_atR rd' a s.
Proof.
intros rd rd' a s [H1 H2] Hk. split; [|exact H2]. apply (pcb_rabytes_kept rd); [exact H1|].
intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply Hk. lia.
Qed.
Lemma pcb_acall_at_kept : forall bl bl' (rd rd' : reader) a c P, acall_at bl rd a c P ->
(forall pn, In pn P -> In pn bl') ->
(forall i, 0 <= i < CALL_OFF_ARGS + 8 * Z.of_nat (length (snd c)) -> rd' (a + i) = rd (a + i)) ->
(forall pn i, In pn P -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
acall_at bl' rd' a c P.
Proof.
intros bl bl' rd rd' a c P (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hbl Ha Hp.
unfold acall_at. unfold CALL_OFF_ARGS, CALL_OFF_FN, CALL_OFF_NARGS in *.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
split; [apply (pcb_aval_mem_kept rd); [exact H4 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [apply (pcb_aval_mem_kept rd); [exact H5 | intros k Hk; rewrite <- Z.add_assoc; apply Ha; apply Nat2Z.inj_lt in Hk; change (Z.of_nat 4) with 4 in Hk; clear - Hk; pose proof (Nat2Z.is_nonneg (length (snd c))); lia]|].
split; [exact H6|].
intros k s pn Hs Hpn. destruct (H7 k s pn Hs Hpn) as (G1 & G2 & G3 & G4 & G5).
pose proof (proj1 (nth_error_Some (snd c) k) ltac:(rewrite Hs; discriminate)) as Hk.
split; [apply (pcb_aval_mem_kept rd); [exact G1 | intros j Hj; rewrite <- !Z.add_assoc; apply Ha; lia]|].
split; [exact G2|]. split; [apply Hbl; exact (nth_error_In _ _ Hpn)|]. split; [exact G4|].
apply (pcb_rastr_kept rd); [exact G5 | intros i Hi; apply Hp; [exact (nth_error_In _ _ Hpn) | lia]].
Qed.
Lemma pcb_aanswer_at_kept : forall bl bl' (rd rd' : reader) gr t q, aanswer_at bl rd gr t q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall i, 0 <= i < 8 -> rd' (gr + OFF_ANSWER + i) = rd (gr + OFF_ANSWER + i)) ->
(forall pn i, q = Some pn -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
aanswer_at bl' rd' gr t q.
Proof.
intros bl bl' rd rd' gr t q H Hbl Ha Hp. destruct t as [x|], q as [pn|]; cbn in H |- *; try exact H.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6).
  split; [apply (pcb_aval_mem_kept rd); [exact A1 | intros k Hk; apply Ha; lia]|].
  split; [exact A2|]. split; [exact (Hbl pn eq_refl)|]. split; [exact A4|]. split; [|exact A6].
  apply (pcb_rastr_kept rd); [exact A5 | intros i Hi; apply (Hp pn i eq_refl); lia].
- apply (pcb_aval_mem_kept rd); [exact H | intros k Hk; apply Ha; lia].
Qed.
Lemma pcb_areply_at_kept : forall bl bl' (rd rd' : reader) gr y q, areply_at bl rd gr y q ->
(forall pn, q = Some pn -> In pn bl') ->
(forall i, 0 <= i < 16 -> rd' (gr + OFF_REPLY + i) = rd (gr + OFF_REPLY + i)) ->
(forall pn i, q = Some pn -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
areply_at bl' rd' gr y q.
Proof.
intros bl bl' rd rd' gr y q H Hbl Ha Hp. unfold OFF_REPLY_SIZE, OFF_REPLY in *.
destruct y as [x|], q as [pn|]; cbn in H |- *; try exact H.
- destruct H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  split; [apply (pcb_aval_mem_kept rd); [exact A1 | intros k Hk; unfold OFF_REPLY; apply Ha; lia]|].
  split; [apply (pcb_aval_mem_kept rd); [exact A2 | intros k Hk; unfold OFF_REPLY_SIZE;
    replace (gr + 936 + Z.of_nat k) with (gr + 928 + (8 + Z.of_nat k)) by lia; apply Ha; lia]|].
  split; [exact A3|]. split; [exact A4|]. split; [exact (Hbl pn eq_refl)|]. split; [exact A6|]. split; [|exact A8].
  apply (pcb_rabytes_kept rd); [exact A7 | intros i Hi; apply (Hp pn i eq_refl); lia].
- destruct H as (A1 & A2).
  split; [apply (pcb_aval_mem_kept rd); [exact A1 | intros k Hk; unfold OFF_REPLY; apply Ha; lia]|].
  apply (pcb_aval_mem_kept rd); [exact A2 | intros k Hk; unfold OFF_REPLY_SIZE;
    replace (gr + 936 + Z.of_nat k) with (gr + 928 + (8 + Z.of_nat k)) by lia; apply Ha; lia].
Qed.
Lemma pcb_lay_calls_in : forall Q i P pn, nth_error (l_calls Q) i = Some P -> In pn P -> In pn (lay_blocks Q).
Proof.
intros Q i P pn HP Hpn. unfold lay_blocks. apply in_or_app. left. apply in_concat. exists P.
split; [exact (nth_error_In _ _ HP) | exact Hpn].
Qed.
Lemma pcb_lay_spill_in : forall Q pn, In pn (l_spill Q) -> In pn (lay_blocks Q).
Proof. intros Q pn H. unfold lay_blocks. apply in_or_app. right. apply in_or_app. left. exact H. Qed.
Lemma pcb_lay_answer_in : forall Q pn, l_answer Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. left. left. reflexivity.
Qed.
Lemma pcb_lay_reply_in : forall Q pn, l_reply Q = Some pn -> In pn (lay_blocks Q).
Proof.
intros Q pn H. unfold lay_blocks. rewrite H. apply in_or_app. right. apply in_or_app. right.
apply in_or_app. right. left. reflexivity.
Qed.

(* g_rec.state := v, every other byte of g_rec and record.spill and every byte of the recorder's blocks kept *)
Lemma pcb_arep_state : forall bl bl' (rd rd' : reader) R Q v,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 v -> 0 <= v < 2 ^ 64 ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
arep_at bl' rd' A_G_REC A_REC_SPILL (set_state R v) Q.
Proof.
intros bl bl' rd rd' R Q v HA Hv Hvr HK HKB Hbl.
destruct HA as (Hg8 & Hs8 & Hap & HC & HAN & HRP & HSC & HOWN).
destruct HC as (Hlen16 & HlQ & HNC & HCi & HSp & HSpM).
destruct HSC as (S1 & S2 & S3 & S4 & S5 & R1 & R2 & R3 & R4 & R5).
assert (KG : forall o, 0 <= o < REC_SIZE -> ~ (OFF_STATE <= o < OFF_STATE + 8) -> rd' (A_G_REC + o) = rd (A_G_REC + o)).
{ intros o Ho Hn. apply HK; [left; lia | lia]. }
assert (KGv : forall o (n : nat) w, aval_mem rd (A_G_REC + o) n w -> 0 <= o -> o + Z.of_nat n <= REC_SIZE ->
  (o + Z.of_nat n <= OFF_STATE \/ OFF_STATE + 8 <= o) -> aval_mem rd' (A_G_REC + o) n w).
{ intros o n w H Ho1 Ho2 Ho3. apply (pcb_aval_mem_kept rd); [exact H|].
  intros k Hk. rewrite <- Z.add_assoc. apply KG; lia. }
assert (KS : forall o, 0 <= o < SC_SIZE -> rd' (A_REC_SPILL + o) = rd (A_REC_SPILL + o)).
{ intros o Ho. apply HK; [right; lia|]. unfold A_REC_SPILL, A_G_REC, OFF_STATE, SC_SIZE in *. lia. }
unfold arep_at, ag1_calls, ag1_scalars.
cbn [set_state r_calls r_spill r_answer r_reply r_refuse r_code r_nreplies r_state r_host].
split; [exact Hg8|]. split; [exact Hs8|]. split; [exact Hap|].
split.
{ split; [exact Hlen16|]. split; [exact HlQ|]. split.
  { apply (KGv OFF_NCALLS 4%nat); [exact HNC | | |]; unfold OFF_NCALLS, OFF_STATE, REC_SIZE; lia. }
  split.
  { intros i c P Ec EP. destruct (HCi i c P Ec EP) as [HAc HFc]. split; [|exact HFc].
    assert (Hi : (i < 16)%nat)
      by (pose proof (proj1 (nth_error_Some (r_calls R) i) ltac:(rewrite Ec; discriminate)); lia).
    apply (pcb_acall_at_kept bl bl' rd rd'); [exact HAc | | |].
    - intros pn Hpn. apply Hbl. exact (pcb_lay_calls_in Q i P pn EP Hpn).
    - intros j Hj. pose proof HAc as (_ & Hc6 & _). unfold CALL_OFF_ARGS in Hj.
      rewrite <- Z.add_assoc, <- Z.add_assoc. apply KG; unfold OFF_CALLS, CALL_SIZE, OFF_STATE, REC_SIZE in *; lia.
    - intros pn j Hpn Hj. apply HKB; [exact (pcb_lay_calls_in Q i P pn EP Hpn) | exact Hj]. }
  split; [|exact HSpM].
  apply (pcb_acall_at_kept bl bl' rd rd'); [exact HSp | | |].
  - intros pn Hpn. apply Hbl. exact (pcb_lay_spill_in Q pn Hpn).
  - intros j Hj. pose proof HSp as (_ & Hc6 & _). unfold CALL_OFF_ARGS in Hj. apply KS. unfold SC_SIZE. lia.
  - intros pn j Hpn Hj. apply HKB; [exact (pcb_lay_spill_in Q pn Hpn) | exact Hj]. }
split.
{ apply (pcb_aanswer_at_kept bl bl' rd rd'); [exact HAN | | |].
  - intros pn Hq. apply Hbl. exact (pcb_lay_answer_in Q pn Hq).
  - intros i Hi. rewrite <- Z.add_assoc. apply KG; unfold OFF_ANSWER, OFF_STATE, REC_SIZE; lia.
  - intros pn i Hq Hi. apply HKB; [exact (pcb_lay_answer_in Q pn Hq) | exact Hi]. }
split.
{ apply (pcb_areply_at_kept bl bl' rd rd'); [exact HRP | | |].
  - intros pn Hq. apply Hbl. exact (pcb_lay_reply_in Q pn Hq).
  - intros i Hi. rewrite <- Z.add_assoc. apply KG; unfold OFF_REPLY, OFF_STATE, REC_SIZE; lia.
  - intros pn i Hq Hi. apply HKB; [exact (pcb_lay_reply_in Q pn Hq) | exact Hi]. }
split; [|exact HOWN].
split; [apply (KGv OFF_REFUSE 4%nat); [exact S1 | | |]; unfold OFF_REFUSE, OFF_STATE, REC_SIZE; lia|].
split; [apply (KGv OFF_CODE 4%nat); [exact S2 | | |]; unfold OFF_CODE, OFF_STATE, REC_SIZE; lia|].
split; [apply (KGv OFF_NREPLIES 4%nat); [exact S3 | | |]; unfold OFF_NREPLIES, OFF_STATE, REC_SIZE; lia|].
split; [exact Hv|].
split; [apply (KGv OFF_HOST 8%nat); [exact S5 | | |]; unfold OFF_HOST, OFF_STATE, REC_SIZE; lia|].
repeat split; first [exact Hvr | lia].
Qed.
(* the same with g_rec.state kept: a change of memory off the recorder's bytes keeps the representation *)
Lemma pcb_arep_kept : forall bl bl' (rd rd' : reader) R Q,
arep_at bl rd A_G_REC A_REC_SPILL R Q ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) -> rd' a = rd a) ->
(forall pn i, In pn (lay_blocks Q) -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn (lay_blocks Q) -> In pn bl') ->
arep_at bl' rd' A_G_REC A_REC_SPILL R Q.
Proof.
intros bl bl' rd rd' R Q HA HK HKB Hbl.
pose proof HA as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & S4 & _ & _ & _ & _ & R4 & _) & _).
rewrite <- (pcb_set_state_id R).
apply (pcb_arep_state bl bl' rd rd' R Q (r_state R) HA); [| exact R4 | intros a Ha _; exact (HK a Ha) | exact HKB | exact Hbl].
apply (pcb_aval_mem_kept rd); [exact S4|]. intros k Hk. apply HK. left. unfold A_G_REC, OFF_STATE, REC_SIZE. lia.
Qed.
(* the recorder's state of the statement (rec_repA) after the store of g_rec.state *)
Lemma pcb_rep_state : forall (B : asyms) ly S ly' S' (rd rd' : reader) R O v,
rec_repA B ly S rd R O ->
aval_mem rd' (A_G_REC + OFF_STATE) 8 v -> 0 <= v < 2 ^ 64 ->
(forall a, (A_G_REC <= a < A_G_REC + REC_SIZE \/ A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE) ->
  ~ (A_G_REC + OFF_STATE <= a < A_G_REC + OFF_STATE + 8) -> rd' a = rd a) ->
(forall pn i, In pn O -> 0 <= i < snd pn -> rd' (fst pn + i) = rd (fst pn + i)) ->
(forall pn, In pn O -> In pn (ablocks B ly' S')) ->
rec_repA B ly' S' rd' (set_state R v) O.
Proof.
intros B ly S ly' S' rd rd' R O v (Q & HA & HOQ) Hv Hvr HK HKB Hbl.
exists Q. split; [|exact HOQ].
apply (pcb_arep_state (ablocks B ly S) (ablocks B ly' S') rd rd' R Q v HA Hv Hvr HK).
- intros pn i Hin Hi. apply HKB; [apply (proj2 (HOQ pn)); exact Hin | exact Hi].
- intros pn Hin. apply Hbl. apply (proj2 (HOQ pn)). exact Hin.
Qed.
(* every block the layout names is a live block of the representation *)
Lemma pcb_arep_lay_in : forall bl rd gr sc R Q pn, arep_at bl rd gr sc R Q -> In pn (lay_blocks Q) ->
In pn bl /\ 1 <= snd pn.
Proof.
intros bl rd gr sc R Q pn (_ & _ & _ & HC & HA & HR & _ & _) Hin.
destruct HC as (_ & HlQ & _ & HCi & HSp & _).
unfold lay_blocks in Hin. apply in_app_or in Hin as [Hin | Hin].
- apply in_concat in Hin as (P & HP & Hpn). apply In_nth_error in HP as (i & Hi).
  assert (Hi' : (i < length (r_calls R))%nat) by (rewrite <- HlQ; apply nth_error_Some; rewrite Hi; discriminate).
  destruct (nth_error (r_calls R) i) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  destruct (HCi i c P Ec Hi) as [(_ & _ & HlP & _ & _ & _ & H7) _].
  apply In_nth_error in Hpn as (k & Hk).
  assert (Hk' : (k < length (snd c))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
  destruct (nth_error (snd c) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
  destruct (H7 k s pn Es Hk) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
- apply in_app_or in Hin as [Hin | Hin].
  + destruct HSp as (_ & _ & HlP & _ & _ & _ & H7).
    apply In_nth_error in Hin as (k & Hk).
    assert (Hk' : (k < length (snd (r_spill R)))%nat) by (rewrite <- HlP; apply nth_error_Some; rewrite Hk; discriminate).
    destruct (nth_error (snd (r_spill R)) k) as [s|] eqn:Es; [|apply nth_error_None in Es; lia].
    destruct (H7 k s pn Es Hk) as (_ & _ & G3 & G4 & _). split; [exact G3 | lia].
  + apply in_app_or in Hin as [Hin | Hin].
    * destruct (l_answer Q) as [q|] eqn:Eq; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_answer R) as [x|]; cbn in HA; [|destruct HA].
      destruct HA as (_ & _ & A3 & A4 & _). split; [exact A3 | lia].
    * destruct (l_reply Q) as [q|] eqn:Eq; [|destruct Hin]. destruct Hin as [<- | []].
      destruct (r_reply R) as [x|]; cbn in HR; [|destruct HR].
      destruct HR as (_ & _ & _ & A4 & A5 & A6 & _). split; [exact A5|].
      destruct x as [|b x]; [exfalso; exact (A4 eq_refl)|]. cbn [length] in A6. lia.
Qed.
Lemma pcb_rep_O_in : forall (B : asyms) ly S rd R O, rec_repA B ly S rd R O ->
forall pn, In pn O -> In pn (ablocks B ly S).
Proof.
intros B ly S rd R O (Q & HA & HOQ) pn Hpn. exact (proj1 (pcb_arep_lay_in _ _ _ _ R Q pn HA (proj1 (HOQ pn) Hpn))).
Qed.

(* --- the state checks and the journal facts ---------------------------------------------------------------- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* the call targets: each callee's entry is BASE + AF_<fn>, from the walk fact cmd_sig_prog (record's is CmdRecAns'
   rca_sig_record) *)
Section s.
Hypothesis SIGP : cmd_sig_prog.
Lemma pcb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (SIGP CS_arg_s (proj1 (proj2 pcb_prog_syms))). reflexivity. Qed.
Lemma pcb_sig_mix_call : SIG CS_mix_call = BASE + AF_mix_call.
Proof. rewrite (SIGP CS_mix_call (proj1 (proj2 (proj2 pcb_prog_syms)))). reflexivity. Qed.
Lemma pcb_sig_answer_code : SIG CS_answer_code = BASE + AF_answer_code.
Proof. rewrite (SIGP CS_answer_code (proj2 (proj2 (proj2 pcb_prog_syms)))). reflexivity. Qed.
End s.


(* the entry (0x8cbe8): every register its own atom, the 32 bytes below sp present *)
Lemma pcb_entry : forall (W : world SEGS) mem (regs : bvmap 5 word) extra,
spZ regs mod 16 = 0 -> 2 ^ 46 + 32 <= spZ regs <= 2 ^ 47 ->
(forall a, spZ regs - 32 <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs extra)) pcb_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_pins_clear)) mem (seg_rom SEGS))).
Proof.
intros W mem regs extra Hsp16 Hsp Hpres.
assert (E2 : bv_unsigned (ew (Eimg (Ereg regs extra)) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
rewrite restrict_mkst_fx. unfold pcb_ss0.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold stack_region. apply Forall_cons; [|apply Forall_nil]. unfold YP09.region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I]. cbn [pcb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | assumption | lia].
Qed.

Hypothesis VOBJS : cmd_val_objs.

(* the object atoms' values: g_rec (s1 from 0x8cc14 on) and record.spill *)
Lemma pcb_grec_val : VAL (A_OBJ 44) = A_G_REC.
Proof. rewrite (VOBJS 44%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

Section e.
Variable B : asyms.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
(* the record facts the walk gives these lemmas (a Theorem Labs lane's CmdRecRest / CmdRecRo lemmas over its image facts) *)
Hypothesis HB : CmdBSyms B.
Hypothesis cmd_prog_img : forall a, Exists (in_zr a) TFIB_PROG_STATIC -> in_img SEGS a.
Hypothesis ROB : ro_below_ofl SEGS RLO RHI.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.
Hypothesis cmd_ro_prog_apart : forall a, in_roP SEGS RLO RHI a -> in_img SEGS a /\ ~ Exists (in_zr a) TFIB_PROG_STATIC.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.

(* ---- the footprint -------------------------------------------------------------------------------------- *)
Lemma pcb_in_PG_grec : forall a, A_G_REC <= a < A_G_REC + REC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.
Lemma pcb_in_PG_spill : forall a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> Exists (in_zr a) TFIB_PROG_STATIC.
Proof. intros a Ha. apply Exists_cons_tl. apply Exists_cons_hd. unfold in_zr. cbn [fst snd]. exact Ha. Qed.
Lemma pcb_inFP_grec : forall O a, A_G_REC <= a < A_G_REC + REC_SIZE -> inFP (pcb_FP O) a.
Proof. intros O a Ha. exists (A_G_REC, A_G_REC + REC_SIZE). split; [left; reflexivity | cbn [fst snd]; exact Ha]. Qed.
Lemma pcb_inFP_spill : forall O a, A_REC_SPILL <= a < A_REC_SPILL + SC_SIZE -> inFP (pcb_FP O) a.
Proof.
intros O a Ha. exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE). split; [right; left; reflexivity | cbn [fst snd]; exact Ha].
Qed.
(* a write of the walk to g_rec: the footprint names it, and it is a program static of the image *)
Lemma pcb_awr_PG : forall STK sp0 O bl0 blc fr0 ly own a,
inFP (pcb_FP O) a -> Exists (in_zr a) TFIB_PROG_STATIC ->
awr_byte SEGS B STK sp0 (pcb_FP O) bl0 blc fr0 ly own a.
Proof.
intros STK sp0 O bl0 blc fr0 ly own a Hfp HPG. right; right; right; right. left.
split; [exact Hfp|]. split; [rewrite (ts_prog B HB); exact HPG | exact (cmd_prog_img a HPG)].
Qed.
(* the region of the store at 0x8cc3c: based at g_rec's object atom, inside g_rec *)
Lemma pcb_awr_cons_grec : forall E r rs STK sp0 O bl0 blc fr0 ly own,
YP09.r_base r = Some (A_OBJ 44) -> img_env VAL A_LIM E ->
0 <= YP09.r_wlo r -> YP09.r_whi r <= REC_SIZE ->
awr_ok SEGS B E rs STK sp0 (pcb_FP O) bl0 blc fr0 ly own -> awr_ok SEGS B E (r :: rs) STK sp0 (pcb_FP O) bl0 blc fr0 ly own.
Proof.
intros E r rs STK sp0 O bl0 blc fr0 ly own Hb HEI Hlo Hhi H.
eapply awr_ok_cons_gen with (n := A_OBJ 44) (b := A_G_REC); [exact Hb | | | exact H].
- rewrite (HEI (A_OBJ 44) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)). exact pcb_grec_val.
- intros a Ha. assert (Ha' : A_G_REC <= a < A_G_REC + REC_SIZE) by lia.
  exact (pcb_awr_PG STK sp0 O bl0 blc fr0 ly own a (pcb_inFP_grec O a Ha') (pcb_in_PG_grec a Ha')).
Qed.

(* ---- what a journal with the call's footprint keeps ------------------------------------------------------ *)
Lemma pcb_inFP_inv : forall O a, inFP (pcb_FP O) a ->
Exists (in_zr a) TFIB_PROG_STATIC \/ exists pn, In pn O /\ fst pn <= a < fst pn + req_size (snd pn).
Proof.
intros O a (r & Hr & Ha). destruct Hr as [<- | [<- | Hr]]; cbn [fst snd] in Ha.
- left. apply pcb_in_PG_grec. exact Ha.
- left. apply pcb_in_PG_spill. exact Ha.
- right. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hin). exists (p, n). split; [exact Hin | exact Ha].
Qed.
(* a byte of a live block the recorder does not own is kept by the journal of the call *)
Lemma pcb_kept_heap : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k q m i,
ajournal SEGS B STK sp0 (pcb_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
In (q, m) (ablocks B ly S) -> ~ In (q, m) O -> In (q, m) (ablocks B ly' S') -> 0 <= i < req_size m ->
rdW W' mem' (q + i) = rdW W mem (q + i).
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k q m i HJ HAR HO Hin HnO Hin' Hi.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HBLK & _).
apply (HBLK q m i Hin Hin' Hi). intros Hfp.
destruct (pcb_inFP_inv O (q + i) Hfp) as [HPG | ([p n] & HinO & Ha)].
- exact (recb_heap_noimg_m B ly S W mem md q m (q + i) HAR Hin ltac:(lia) (cmd_prog_img _ HPG)).
- assert (Hne : (q, m) <> (p, n)) by (intros E; apply HnO; rewrite E; exact HinO).
  pose proof (sep_blocks SEGS B LAWS ly S W mem md q m p n HAR Hin (HO _ HinO) Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D, Ha. lia.
Qed.
(* arodata_okP survives a journal with the call's footprint (CmdBase.v arodata_ok_journalP) *)
Lemma pcb_aro_kept : forall STK sp0 O ly S (W : world SEGS) mem md own ly' S' (W' : world SEGS) mem' md' k,
ajournal SEGS B STK sp0 (pcb_FP O) ly S W mem md own ly' S' W' mem' md' k -> AR SEGS B ly S W mem md ->
(forall pn, In pn O -> In pn (ablocks B ly S)) ->
arodata_okP SEGS RLO RHI B (rdW W mem) -> arodata_okP SEGS RLO RHI B (rdW W' mem').
Proof.
intros STK sp0 O ly S W mem md own ly' S' W' mem' md' k HJ HAR HO HR.
apply (arodata_ok_journalP SEGS RLO RHI RELRO_IMG (RO := ROB) B STK sp0 (pcb_FP O) ly S W mem md own ly' S' W' mem' md' k HJ);
[| exact HR].
intros a Hro Hfp. destruct (cmd_ro_prog_apart a Hro) as [Himg HnPG].
destruct (pcb_inFP_inv O a Hfp) as [HPG | ([p n] & Hin & Ha)]; [exact (HnPG HPG)|].
exact (recb_heap_noimg_m B ly S W mem md p n a HAR (HO _ Hin) Ha Himg).
Qed.

(* ---- the program's statics and the callees' journals --------------------------------------------------- *)
(* a callee's journal keeps a byte of the program's statics outside its footprint *)
Lemma pcb_callee_keeps_PG : forall STK1 sp1 FP1 lyc Sc (W : world SEGS) memc mdc own ly2 S2 (W2 : world SEGS) mem2 md2 k1 a,
ajournal SEGS B STK1 sp1 FP1 lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 k1 -> ~ YI16.sink_open_fp FP1 ->
~ inFP FP1 a -> Exists (in_zr a) TFIB_PROG_STATIC -> rdW W2 mem2 a = rdW W memc a.
Proof.
intros STK1 sp1 FP1 lyc Sc W memc mdc own ly2 S2 W2 mem2 md2 k1 a HJ Hso Hfp HP.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HIMG & _).
destruct (recb_prog_unowned_m B HB cmd_prog_img a HP) as (Himg & Hown & Herr).
apply HIMG; [exact Himg | exact Hown | exact Herr |]. split; [intros H; exfalso; exact (Hso H) | exact Hfp].
Qed.
Lemma pcb_region_kept_PG : forall E (W W2 : world SEGS) m m2 nn b lo hi wlo whi cs,
bv_unsigned (ew E nn) = b ->
(forall a, b + lo <= a < b + hi -> rdW W2 m2 a = rdW W m a) ->
(forall a, b + wlo <= a < b + whi -> writable_at SEGS (mrestrict (w_H W2) m2) a) ->
region_kept SEGS E (mrestrict (w_H W) m) (mrestrict (w_H W2) m2) (YP09.mkRegion (Some nn) lo hi wlo whi cs).
Proof.
intros E W W2 m m2 nn b lo hi wlo whi cs U Hv Hw.
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U.
- intros a Ha. apply (mbyte_of_aview SEGS). exact (Hv a Ha).
- intros a Ha _. exact (Hw a Ha).
Qed.

End e.
End f.
End d.
