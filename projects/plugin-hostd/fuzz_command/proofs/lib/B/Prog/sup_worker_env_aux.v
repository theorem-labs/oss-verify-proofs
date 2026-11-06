(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the parts of sup_worker_env's ASan+UBSan walk (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan) that need no callee statement: the walk's entry in B's listing, the listing's 34 slots,
   the symbolic state and seed of the entry, the call targets, the model's step, and the verb literal "worker_env"
   with the premise rec_shape_of's statement (lib/B/Prog/rec_shape_of_c.v:92-95, a Theorem Labs lane fc8bcbd8b42) asks of it. In
   the form of lib/B/Prog/sup_reset_aux.v (a working branch c79a9f2daf7, whose B code is this one's with
   one call of arg_s for three, a 32-byte frame for 48, FN 10 for 16 and the verb 0x21e00 for 0x21f00), after the A
   walk lib/A/Prog/sup_worker_env.v (a working branch 65a6716e4ad: sup_worker_env_s4.v:2151-2250 swe_r3_vb,
   swe_r3_fits, swe_r3_verb), re-derived on B's code, which differs from A's (below). *)

(* sup_worker_env on B (recorder.c:454-462; entry BASE + AF_sup_worker_env = 0x8c13c, 34 instructions, 136 bytes;
   measured with capstone 5.0.7 on the .symtab entry of fuzz_command.asan-ubsan, sha256
   658cefbe806b535ba1fbe5a37c8efe02099fc39c326f300e9b1c969d479df401; listing lib/B/Prog/CmdList.v:5970-6003):
     0x8c13c .. 0x8c160  addi sp,sp,-48; sd ra,40(sp); sd s0,32(sp); sd s1,24(sp); sd s2,16(sp); sd s3,8(sp);
                         mv s0,a2; mv s1,a1; mv s2,a0; li a0,16
     0x8c164             jal record                      (0x8a728)
     0x8c168 .. 0x8c16c  mv s3,a0; mv a1,s2
     0x8c170             jal arg_s                       (0x8a820, format)
     0x8c174 .. 0x8c178  mv a0,s3; mv a1,s1
     0x8c17c             jal arg_s                       (0x8a820, cpus)
     0x8c180 .. 0x8c184  mv a0,s3; mv a1,s0
     0x8c188             jal arg_s                       (0x8a820, nice)
     0x8c18c .. 0x8c194  auipc a0,0xfff96; addi a0,a0,-652 (= 0x21f00, "worker_env"); li a1,10
     0x8c198             jal rec_shape_of                (0x896d4)
     0x8c19c .. 0x8c1bc  li a2,1; mv a1,a0; mv a0,s3; ld ra,40(sp); ld s0,32(sp); ld s1,24(sp); ld s2,16(sp);
                         ld s3,8(sp); addi sp,sp,48
     0x8c1c0             j answer                        (0x8aa10, the tail jump)
   No branch, no loop, no inline ASan check (no call of an __asan_report entry), no UBSan trap site (no unimp or
   ebreak), no load or store through an auipc base (the one auipc forms the literal's address: listing PHi a0 177,
   then PAddHi a0 a0 177 (A_OBJ 76) 0x0, which sets a0 to the object atom; cmd_val_objs gives its value, and the
   A_HI value 0x2218c is not used). Its only caller is verbs_receive (`jal` at 0x8d600). A's code (0x8c060, 149
   instructions) inlined record() (the slot and spill arms, rec_calls_free) and the stores of fn, nargs and args[0..2]
   with their 8 inline checks (report sites 0x8c248 .. 0x8c2b0), and called xstrdup three times; B calls record() and
   arg_s() instead, which carry those checks themselves. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import String ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05 YC5d YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require Import YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdSyms CmdAddr CmdList CmdPa CmdPaLib.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaCall PaCallRun PaLibF PaLibG PaLibH PaSB PaDenot.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdGlob CmdBase CmdChk CmdRep CmdObj CmdRo.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the walk's entry in the listing *)
Definition SWEB_E : Z := AF_sup_worker_env.       (* the entry (0x8c13c) *)
Definition SWEB_FRAME : Z := 48.
(* the function the call records (REC_WORKER_ENV, the `li a0,16` before the call of record) *)
Definition SWEB_FN : Z := 16.
(* the verb "worker_env": the image literal at 0x21f00 (CmdRo's RO_lit_21f00, .str.14), the listing's object 76 *)
Definition SWEB_VERB : Z := 0x21f00.
Definition SWEB_VOBJ : nat := A_OBJ 76.
Definition sweb_verb : list byte := bstr "worker_env"%string.

(* the function's 34 slots in B's listing (lib/B/Prog/CmdList.v:5970-6003) *)
Definition sweb_code : ptable csym := [
PW 0xfd010113; PW 0x2113423; PW 0x2813023; PW 0x913c23; PW 0x1213823; PW 0x1313423;
PW 0x60413; PW 0x58493; PW 0x50913; PW 0x1000513;
PCall CS_record (1%bv : bv 5);
PW 0x50993; PW 0x90593;
PCall CS_arg_s (1%bv : bv 5);
PW 0x98513; PW 0x48593;
PCall CS_arg_s (1%bv : bv 5);
PW 0x98513; PW 0x40593;
PCall CS_arg_s (1%bv : bv 5);
PHi (10%bv : bv 5) 177; PAddHi (10%bv : bv 5) (10%bv : bv 5) 177 (A_OBJ 76) 0x0; PW 0xa00593;
PCall CS_rec_shape_of (1%bv : bv 5);
PW 0x100613; PW 0x50593; PW 0x98513; PW 0x2813083; PW 0x2013403; PW 0x1813483; PW 0x1013903; PW 0x813983;
PW 0x3010113;
PTail CS_answer].

Lemma sweb_listing : firstn 34 (skipn (Z.to_nat (SWEB_E / 4)) cmd_listing) = sweb_code.
Proof. vm_compute. reflexivity. Qed.

(* the call targets and the tail jump, against the image's address map (CmdAddr.v's cmd_sigma), and the entry *)
Lemma sweb_callees :
cmd_sigma CS_sup_worker_env = 0x8c13c /\ cmd_sigma CS_record = 0x8a728 /\ cmd_sigma CS_arg_s = 0x8a820 /\
cmd_sigma CS_rec_shape_of = 0x896d4 /\ cmd_sigma CS_answer = 0x8aa10 /\ cmd_text + SWEB_E = 0x8c13c.
Proof. vm_compute. repeat split. Qed.

(* the callees' offsets from the listing's base, and the four callees are program functions of the listing *)
Lemma sweb_af : cmd_af CS_record = AF_record /\ cmd_af CS_arg_s = AF_arg_s /\
cmd_af CS_rec_shape_of = AF_rec_shape_of /\ cmd_af CS_answer = AF_answer.
Proof. vm_compute. repeat split; reflexivity. Qed.

Lemma sweb_prog_syms : In CS_record cmd_prog_syms /\ In CS_arg_s cmd_prog_syms /\
In CS_rec_shape_of cmd_prog_syms /\ In CS_answer cmd_prog_syms.
Proof. vm_compute. repeat split; repeat (first [left; reflexivity | right]). Qed.

(* the model's step: record(16) with the copies of format, cpus and nice, the verb's shape, answer with changes = 1
   (RecModel.v:162-163) *)
Lemma sweb_m : forall R format cpus nice,
sup_worker_env_m R format cpus nice =
rec_answer (rec_record R SWEB_FN [sarg format; sarg cpus; sarg nice]) (SWEB_FN, [sarg format; sarg cpus; sarg nice])
  (shape_of sweb_verb) true.
Proof. reflexivity. Qed.

Lemma sweb_verb_len : Z.of_nat (length sweb_verb) = 10.
Proof. reflexivity. Qed.

Lemma sweb_verb_lit : RO_lit_21f00 = sweb_verb ++ [Z_to_bv 8 0].
Proof. vm_compute. reflexivity. Qed.

(* the verb has no NUL byte *)
Lemma sweb_verb_nonul : ~ In (Z_to_bv 8 0) sweb_verb.
Proof.
intros Hz. apply (in_map bv_unsigned) in Hz. vm_compute in Hz.
repeat (destruct Hz as [Hz|Hz]; [discriminate Hz|]). exact Hz.
Qed.

(* the shape answer instantiates fits its buffer (answer_c.v:125; A: swe_r3_fits) *)
Lemma sweb_fits : fits (shape_of sweb_verb).
Proof. unfold fits. vm_compute. congruence. Qed.

Lemma sweb_bytes_prefix : forall (rd : reader) a l l2, abytes_atR rd a (l ++ l2) -> abytes_atR rd a l.
Proof. intros rd a l l2 H i Hi. rewrite (H i) by (rewrite length_app; lia). rewrite app_nth1 by exact Hi. reflexivity. Qed.

(* the conjunct of a long conjunction that holds the literal address [a]: a syntactic search that drops the leading
   conjuncts of H in place, so no conjunct is unified with the goal and no nested proj2 term is retyped
   (sup_lv2_worker_set_aux.v's slw_projz) *)
Local Ltac sweb_projz H a :=
  repeat lazymatch type of H with
  | ?A /\ _ => lazymatch A with context [a] => fail | _ => destruct H as [_ H] end
  end;
  lazymatch type of H with
  | _ /\ _ => exact (proj1 H)
  | _ => exact H
  end.

(* the verb's 11 bytes (10 and the terminator) are the image's wherever cmd_ro_ok holds *)
Lemma sweb_lit_at : forall rd, cmd_ro_ok rd -> abytes_atR rd SWEB_VERB RO_lit_21f00.
Proof. intros rd [HBY _]. unfold cmd_ro_bytes in HBY. unfold SWEB_VERB. sweb_projz HBY 0x21f00. Qed.

Lemma sweb_verb_at : forall rd, cmd_ro_ok rd -> astr_atR rd SWEB_VERB sweb_verb.
Proof.
intros rd H. pose proof (sweb_lit_at rd H) as HL. rewrite sweb_verb_lit in HL. split; [exact HL | exact sweb_verb_nonul].
Qed.

(* its 10 bytes, the form rec_shape_of's premise asks *)
Lemma sweb_verb_bytes : forall rd, cmd_ro_ok rd -> abytes_atR rd SWEB_VERB sweb_verb.
Proof. intros rd H. exact (sweb_bytes_prefix _ _ _ _ (proj1 (sweb_verb_at rd H))). Qed.

(* its 11 bytes are read-only wherever cmd_ro_in holds *)
Lemma sweb_verb_ro : forall ro : Z -> Prop, cmd_ro_in ro -> forall i, 0 <= i < 11 -> ro (SWEB_VERB + i).
Proof. intros ro HRI. unfold cmd_ro_in in HRI. unfold SWEB_VERB. sweb_projz HRI 0x21f00. Qed.

(* a byte range none of a concrete list of ranges holds *)
Lemma sweb_unowned_rng : forall a n (l : list (Z * Z)),
forallb (fun r => (a + n <=? fst r) || (fst r + snd r <=? a)) l = true ->
forall i, 0 <= i < n -> ~ Exists (in_zr (a + i)) l.
Proof.
intros a n l Hb i Hi Hex. apply Exists_exists in Hex as (r & Hr & Hz).
rewrite forallb_forall in Hb. specialize (Hb r Hr). unfold in_zr in Hz.
apply orb_true_iff in Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
Qed.

(* membership in a long list of integers, decided by computation on a closed goal *)
Lemma sweb_z_in : forall (e : Z) l, existsb (Z.eqb e) l = true -> In e l.
Proof.
intros e l. induction l as [|x l IH]; cbn [existsb In]; [discriminate|].
intros H. apply orb_true_iff in H as [H|H]; [left; apply Z.eqb_eq in H; symmetry; exact H | right; exact (IH H)].
Qed.

(* the record's checks of the literal (lib/B/Prog/CmdChk.v over lib/B/YF0m.v) and its end among CmdRo's literal ends *)
Lemma sweb_verb_addr : cmd_addr_b SWEB_VERB 11 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweb_verb_hull : cmd_hull_b SWEB_VERB 11 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sweb_verb_end : In (SWEB_VERB + Z.of_nat (length sweb_verb)) cmd_ro_ends.
Proof. apply sweb_z_in. vm_compute. reflexivity. Qed.
Lemma sweb_verb_unowned : forall i, 0 <= i < 11 ->
~ Exists (in_zr (SWEB_VERB + i)) Tfib_owned_static /\ ~ (TFIB_ERRNO <= SWEB_VERB + i < TFIB_ERRNO + 4).
Proof.
intros i Hi. split; [apply (sweb_unowned_rng SWEB_VERB 11); [vm_compute; reflexivity | exact Hi]|].
unfold TFIB_ERRNO, SWEB_VERB. lia.
Qed.

(* atoms: the 32 registers at the entry, then the entry's ra, s0, s1, s2, s3 (unused by the walk, kept for the
   seed's form) *)
Definition sweb_saved : list Z := [1; 8; 9; 18; 19].
Definition sweb_extra (regs0 : bvmap 5 word) : list word := map (fun r => getr regs0 (Z_to_bv 5 r)) sweb_saved.
Definition sweb_facts : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4)] [] [].

(* the frame at the entry: the prologue writes it, nothing after the prologue writes it *)
Definition sweb_stack0 : YP09.region := YP09.mkRegion (Some 2%nat) (- SWEB_FRAME) 0 (- SWEB_FRAME) 0 [].
Definition sweb_ssA : sstate := mkSS SWEB_E sr_atoms [sweb_stack0] None sweb_facts.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.

(* the literal's object atom has the literal's address *)
Lemma sweb_vobj : cmd_val_objs -> VAL SWEB_VOBJ = SWEB_VERB.
Proof. intros VOBJS. unfold SWEB_VOBJ. rewrite (VOBJS 76%nat ltac:(vm_compute; lia)). vm_compute. reflexivity. Qed.

(* every atom of the walk's environment: the registers at the entry, then the entry's ra, s0, s1, s2, s3 *)
Definition sweb_E (regs0 : bvmap 5 word) : env := Eimg (Ereg regs0 (sweb_extra regs0)).

Lemma sweb_afact : forall E m v lo hi al,
ew E m = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> lo <= v <= hi -> v mod 2 ^ al = 0 -> 0 <= al <= 64 ->
afact_ok E m (mkAF lo hi al).
Proof.
intros E m v lo hi al Hm Hv Hlh Hal Hal2. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Hm, unsigned_lit_small by exact Hv. split; [exact Hlh | split; [exact Hal | exact Hal2]].
Qed.

Lemma sweb_E_reg : forall regs0 k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (sweb_E regs0) k = getr regs0 r.
Proof.
intros regs0 k r Hk. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold sweb_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk.
Qed.

Lemma sweb_E_img : forall regs0, img_env VAL A_LIM (sweb_E regs0).
Proof. intros. unfold sweb_E. apply Eimg_env. Qed.

(* the environment agrees with the entry's registers on the 32 register atoms *)
Lemma sweb_E_agree : forall regs0, env_agree 32 (Ereg regs0 (sweb_extra regs0)) (sweb_E regs0).
Proof. intros regs0. split; [intros n Hn; unfold sweb_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]. Qed.

Lemma sweb_facts_ok : forall regs0,
2 ^ 46 <= bv_unsigned (getr regs0 2) <= 2 ^ 47 -> bv_unsigned (getr regs0 2) mod 16 = 0 ->
facts_ok (sweb_E regs0) sweb_facts.
Proof.
intros regs0 Hsp Hsp16.
set (E := sweb_E regs0).
assert (E2 : ew E 2 = Z_to_bv 64 (bv_unsigned (getr regs0 2)))
  by (subst E; rewrite (sweb_E_reg _ 2 2%bv eq_refl); symmetry; apply Z_to_bv_bv_unsigned).
unfold facts_ok, sweb_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
split; [|split; [exact I | exact I]].
split; [|exact I].
apply (sweb_afact E 2%nat (bv_unsigned (getr regs0 2))); [exact E2 | lia | lia | change (2 ^ 4) with 16; exact Hsp16 | lia].
Qed.

(* the seed at the entry: the frame the prologue writes *)
Lemma sweb_seed_entry : forall (W : world SEGS) (regs : bvmap 5 word) mem,
2 ^ 46 <= spZ regs <= 2 ^ 47 -> spZ regs mod 16 = 0 ->
(forall a, spZ regs - SWEB_FRAME <= a < spZ regs -> apresent (w_H W) mem a) ->
st_ok_pi SEGS VAL (sweb_E regs) sweb_ssA
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + SWEB_E)) mem (seg_rom SEGS))).
Proof.
intros W regs mem Hsp Hsp16 Hpres.
set (E := sweb_E regs).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (sweb_E_reg _ 2 2%bv eq_refl); reflexivity).
unfold sweb_ssA. rewrite restrict_mkst_fx.
apply pa_entry_st_ok_full.
- subst E. unfold sweb_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold sweb_stack0.
  repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  cbn [base_val]. rewrite E2. unfold SWEB_FRAME in *. split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
  constructor.
- apply pairwise_disjoint_of_extents. unfold sweb_stack0, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  cbn [zpairwise_disjoint zall_disjoint]. repeat split.
- exact (sweb_facts_ok regs ltac:(unfold spZ in Hsp; lia) Hsp16).
Qed.

Section e.
Variable B : asyms.
(* the per-binary allocator record (a Theorem Labs lane's lib/B/YF0m.v), under its canonical name (RECB-NAMED-HYPS.md) *)
Hypothesis HB : CmdBSyms B.

(* --- rec_shape_of's verb premise (rec_shape_of_c.v:92-95) at the literal, call at 0x8c198 ------------------ *)
(* the read-only arm of astr_argA (CmdRep.v:149-152): every byte read-only (cmd_ro_in), owned by no runtime entry
   and not the errno cell (the record's lists, ts_owned / ts_errno), the record's checks cmd_addr_b / cmd_hull_b and
   the literal's end among CmdRo's literal ends, each by computation *)
Lemma sweb_verb_ok : forall ly S (W : world SEGS) mem,
cmd_ro_ok (rdW W mem) -> cmd_ro_in (in_roP SEGS RLO RHI) ->
Z.of_nat (length sweb_verb) <= 16 ->
abytes_atR (rdW W mem) SWEB_VERB sweb_verb /\
(in_blockA (ablocks B ly S) SWEB_VERB (Z.of_nat (length sweb_verb)) \/
 astr_argA B ly S (rdW W mem) (in_roP SEGS RLO RHI) [] SWEB_VERB (Some sweb_verb)).
Proof.
intros ly S W mem HROK HRI _.
split; [exact (sweb_verb_bytes _ HROK)|].
right. cbn [astr_argA]. rewrite sweb_verb_len. split; [unfold SWEB_VERB; lia|]. split; [exact (sweb_verb_at _ HROK)|].
split; [unfold LMAX; lia|]. right. split; [|split; [exact sweb_verb_addr | split; [exact sweb_verb_hull|]]].
- intros i Hi. split; [exact (sweb_verb_ro _ HRI i Hi)|]. rewrite (ts_owned B HB), (ts_errno B HB).
  exact (sweb_verb_unowned i Hi).
- rewrite <- sweb_verb_len. exact sweb_verb_end.
Qed.

(* --- the call targets: arg_s (0x8c170, 0x8c17c, 0x8c188), rec_shape_of (0x8c198), answer (0x8c1c0); record's
   (0x8c164) is the kit's lib/B/Prog/CmdRecAns.v rca_sig_record ------------------------------------------- *)
Section s.
(* the call targets of the program functions (lib/B/Prog/CmdObj.v cmd_sig_prog), under the name of a Theorem Labs lane's lemma
   that proves it at the pinned image (lib/B/Prog/CmdRecRest.v cmd_sig_prog_PB) *)
Hypothesis cmd_sig_prog_PB : cmd_sig_prog.
Lemma sweb_sig_arg_s : SIG CS_arg_s = BASE + AF_arg_s.
Proof. rewrite (cmd_sig_prog_PB CS_arg_s (proj1 (proj2 sweb_prog_syms))), (proj1 (proj2 sweb_af)). reflexivity. Qed.
Lemma sweb_sig_rso : SIG CS_rec_shape_of = BASE + AF_rec_shape_of.
Proof.
rewrite (cmd_sig_prog_PB CS_rec_shape_of (proj1 (proj2 (proj2 sweb_prog_syms)))), (proj1 (proj2 (proj2 sweb_af))).
reflexivity.
Qed.
Lemma sweb_sig_answer : SIG CS_answer = BASE + AF_answer.
Proof.
rewrite (cmd_sig_prog_PB CS_answer (proj2 (proj2 (proj2 sweb_prog_syms)))), (proj2 (proj2 (proj2 sweb_af))).
reflexivity.
Qed.
End s.
End e.
End f.
End d.
