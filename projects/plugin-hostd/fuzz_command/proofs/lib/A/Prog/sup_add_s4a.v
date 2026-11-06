(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the fifth segment of check_reply's walk (fuzz_command.asan, 0x86d78), the
   strcmp call of the refusal path (0x86fb8) and the branch into the epilogue, ported from
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (the step through a call and back) and A/ACh5.v (a segment that ends
   in another segment's statement), at c8557374ad2e.

   The code of the segment is
     0x86fb8  jal  wrapper_strcmp       a0 = g_rec.reply, a1 = s3 = F + 32, which holds "resp <code>"
     0x86fbc  beqz a0, 0x86ff8          equal: the epilogue; else j 0x870d8, the abort
   The entry facts give `xr = refusal_text (reply_code_a xr)` for a negative code (reply_okA), and the frame holds
   `refusal_text code ++ [0]` (the snprintf step of segment 4), so the two strings are equal, the interceptor
   returns 0, and the abort edge 0x86fc0 is not taken.

   The walk runs with the symbolic regions dropped (`st_ok_pi_submem` with []): the two instructions write no
   memory, so the engine's frame is empty and every byte the walk reads is the byte of the state the segment was
   entered in. The interceptor's own writes are the ones its contract allows, inside its scratch window below sp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_reply_s5.v, with its module names changed; 456 of its 500 lines of code are new or changed and 368 lines of the source are left out. *)
(* sup_add's walk, stage M2 -> M3 (plugin-hostd/fuzz_command, ASan build): the seed, the mid-state and the lemmas
   about memory and registers that the runs and the calls of the stage share.

   The two string arguments the slot still wants: args[2] = a copy of `placement` (or of "-"), args[3] = a copy of
   `client` (or of "-"). Each is a call of xstrdup on the spilled pointer (s1 + 24, s1 + 16) or, when that pointer
   is NULL, on the literal "-" (A_OBJ 53 = 0x21d40), followed by an inline check of the slot's nargs word and of
   the args slot it writes, the load of nargs, nargs := nargs + 1 and the store of the copy's address. The two
   `blt` guards on nargs are not taken: nargs is 2 at M2 and 3 after the first argument.

   Shape: the cgif_file_fuzzer walk (lib/A/ACh2.v), with a seed at every program point the stage re-enters after a
   call: the symbolic state is the registers as atoms (s1 = atom 2, the slot pointer c = atom 22), the two spill
   words of the real frame as atoms 32 (placement) and 33 (client), the slot's nargs word and the args word the
   run writes as regions over atom 22, and one shadow entry for the whole slot (its 56 bytes lie in a zero-shadow
   range of the allocator record, so every inline check is removed by `cmd_addressable_in`). *)
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
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal CmdSyms CmdList CmdPa CmdPaLib PaCall PaDenot PaSB PaLibH.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs RtFormat.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts RecModel RecInv.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
CmdGlob CmdAddr CmdBase CmdRep CmdObj CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import
rec_calls_free_c xstrdup_c arg_i_c mix_call_c hand_back_c answer_c sup_add_c sup_add_s0 sup_add_lem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdRecFacts.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the program points of the stage: the returns of the two calls of xstrdup *)
Definition S4_RET1 : Z := AF_sup_add + 0x218.    (* 0x89fd4 *)
Definition S4_RET2 : Z := AF_sup_add + 0x264.    (* 0x8a020 *)

(* the symbolic state of a seed: the registers as atoms, with s1 (x9) the stack atom 2 and the three slot
   pointers c (x22), c + 4 (x23), c + 8 (x24) over atom 22, and x27 the shadow byte of c + 4 *)
Definition s4_shx (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 o) (SLit 3)) (SOff 20 0).
Definition s4_regs : list sv := Eval vm_compute in
  sr_set (sr_set (sr_set (sr_set sr_atoms 9 (SOff 2 0)) 23 (SOff 22 4)) 24 (SOff 22 8)) 27 (s4_shx 4).
(* the two spilled pointers of the real frame: placement at s1 + 24 (atom 32), client at s1 + 16 (atom 33) *)
Definition s4_spill : YP09.region :=
  YP09.mkRegion (Some 2%nat) 16 32 16 16 [YP09.mkChunk 16 (CVal 8 (SOff 33 0)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))].
Definition s4_nargs (v : Z) : YP09.region := YP09.mkRegion (Some 22%nat) 4 8 4 8 [YP09.mkChunk 4 (CVal 4 (SLit v))].
Definition s4_args (k : Z) : YP09.region :=
  YP09.mkRegion (Some 22%nat) (8 + 8 * k) (16 + 8 * k) (8 + 8 * k) (16 + 8 * k) [].
(* phase 0 (M2): the spill only, read-only; phase 1 (after the first call): the spill, nargs and args[2];
   phase 2 (after the second call): nargs and args[3] *)
Definition s4_rs (ph : nat) (nv : Z) : smem :=
  match ph with
  | 0%nat => [s4_spill]
  | 1%nat => [s4_spill; s4_nargs nv; s4_args 2]
  | _ => [s4_nargs nv; s4_args 3]
  end.
Definition s4_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, mkAF SB SB 0);
           (22%nat, mkAF (A_G_REC + OFF_CALLS) A_REC_SPILL 3)] [] [].
Definition s4_SH : list shent := [mkSHE 22 0 56].
Definition s4_Bx : sv := SOff 20 0.
Definition s4_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition s4_ss (pc : Z) (rs : smem) : sstate := mkSS pc s4_regs rs None s4_facts.
(* the slot the call records in: the next table slot, or record.spill *)
Definition s4_cok (c : Z) : Prop :=
  (A_G_REC + OFF_CALLS <= c /\ c + 56 <= A_G_REC + OFF_ANSWER) \/ c = A_REC_SPILL.
(* the registers every run and call of the stage keeps *)
Definition s4_kz : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

Lemma s4_c_range : forall c, s4_cok c -> 0x5e3750 <= c /\ c + 56 <= 0x5e3c18 /\ c <= 0x5e3be0.
Proof. intros c [[H1 H2] | ->]; unfold A_G_REC, OFF_CALLS, OFF_ANSWER, A_REC_SPILL in *; lia. Qed.
Lemma s4_c_of_R : forall R, s4_cok (sa_c R) /\ sa_c R mod 8 = 0.
Proof.
intros R. unfold sa_c. destruct (Nat.ltb_spec (length (r_calls R)) 16) as [Hlt | Hge].
- split; [left | ]; unfold A_G_REC, OFF_CALLS, CALL_SIZE, OFF_ANSWER;
  [ split; [lia |]; assert (Z.of_nat (length (r_calls R)) <= 15) by lia; lia
  | rewrite Z.add_mod, Z.mul_mod by lia; cbn; rewrite Z.mod_0_l by lia; reflexivity ].
- split; [right; reflexivity | reflexivity].
Qed.
Lemma s4_kz_cs : forall z, In z s4_kz -> acallee_saved z.
Proof. intros z Hz. unfold s4_kz in Hz. unfold acallee_saved. cbn [In] in Hz. lia. Qed.
(* a register the stage keeps, through an equation over s4_kz *)
Lemma s4_reg_tr : forall (r1 r2 : bvmap 5 word) (r : bv 5) (v : word) (z : Z),
  getr r1 r = v -> (forall z', In z' s4_kz -> getr r2 (Z_to_bv 5 z') = getr r1 (Z_to_bv 5 z')) ->
  In z s4_kz -> Z_to_bv 5 z = r -> getr r2 r = v.
Proof. intros r1 r2 r v z H HK Hz Hr. subst r. rewrite (HK z Hz). exact H. Qed.
Ltac s4_kr HK H z :=
  exact (s4_reg_tr _ _ _ _ z H HK ltac:(apply lem_in_z; vm_compute; reflexivity) ltac:(apply bv_eq; vm_compute; reflexivity)).
Lemma s4_s1_facts : forall sp0, sp0 mod 16 = 0 -> sa_s1 sp0 = sp0 - 160 \/ sa_s1 sp0 = sp0 - 176.
Proof. intros sp0 H. unfold sa_s1. Z.div_mod_to_equations. lia. Qed.
Lemma s4_s1_al : forall sp0, sa_s1 sp0 mod 32 = 0.
Proof. intros sp0. unfold sa_s1. Z.div_mod_to_equations. lia. Qed.
(* every byte of the slot is a byte of g_rec or of record.spill *)
Lemma s4_in_rec : forall c a, s4_cok c -> c <= a < c + 56 -> in_rec a /\ inFP cmd_PG a.
Proof.
intros c a Hc Ha. destruct Hc as [[H1 H2] | Hs].
- split.
  + left. unfold A_G_REC, OFF_CALLS, OFF_ANSWER, REC_SIZE in *. lia.
  + exists (A_G_REC, A_G_REC + 960). split; [cbn [cmd_PG In]; auto|].
    cbn [fst snd]. unfold A_G_REC, OFF_CALLS, OFF_ANSWER in *. lia.
- split.
  + right. rewrite Hs in Ha. unfold A_REC_SPILL, SC_SIZE in *. lia.
  + exists (A_REC_SPILL, A_REC_SPILL + 56). split; [cbn [cmd_PG In]; auto|].
    cbn [fst snd]. rewrite Hs in Ha. lia.
Qed.
Lemma s4_rec_pg : forall a, in_rec a -> inFP cmd_PG a.
Proof.
intros a Ha. unfold in_rec in Ha. unfold inFP, cmd_PG. destruct Ha as [Ha | Ha].
- exists (A_G_REC, A_G_REC + 960). split; [cbn [In]; auto | cbn [fst snd]; unfold REC_SIZE in Ha; lia].
- exists (A_REC_SPILL, A_REC_SPILL + 56). split; [cbn [In]; auto | cbn [fst snd]; unfold SC_SIZE in Ha; lia].
Qed.
Lemma s4_in_rec_range : forall a, in_rec a -> 0x5e3740 <= a < 0x5e3c18.
Proof. intros a [Ha | Ha]; unfold A_G_REC, REC_SIZE, A_REC_SPILL, SC_SIZE in Ha; lia. Qed.
Lemma s4_inFP : forall c (O : list (Z * Z)) a, s4_cok c -> c <= a < c + 56 -> inFP (sa_FP O) a.
Proof.
intros c O a Hc Ha. unfold sa_FP. destruct Hc as [[H1 H2] | Hs].
- exists (A_G_REC + OFF_CALLS, A_G_REC + OFF_ANSWER + 8).
  split; [cbn [In]; right; left; reflexivity | cbn [fst snd]; lia].
- exists (A_REC_SPILL, A_REC_SPILL + SC_SIZE).
  split; [cbn [In]; right; right; right; left; reflexivity
         | cbn [fst snd]; rewrite Hs in Ha; unfold SC_SIZE; lia].
Qed.
Lemma s4_aval_kept : forall (rd rd' : reader) a (n : nat) v,
  aval_mem rd a n v -> (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> aval_mem rd' a n v.
Proof. intros rd rd' a n v Hv Hk k Hk2. rewrite Hk by lia. apply Hv. exact Hk2. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ cmd_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Lemma s4_aval_of_val : forall H (mem : word -> option byte) a (n : nat) v,
  val_mem SEGS (mrestrict H mem) a n v -> aval_mem (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8.
unfold YG0f.le_byte, YO0f.le_byte. change (2 ^ 8) with 256. apply Z.mod_mod. lia.
Qed.
Lemma s4_val_of_aval : forall H (mem : word -> option byte) a (n : nat) v,
  aval_mem (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
unfold YG0f.le_byte, YO0f.le_byte in *.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Hb; [|discriminate].
cbn in Hv. injection Hv as Hv. rewrite <- Hv, Z_to_bv_bv_unsigned. reflexivity.
Qed.
Definition s4_E (regs1 : bvmap 5 word) (vp vc : Z) : env := Eimg (Ereg regs1 (map (Z_to_bv 64) [vp; vc])).
(* the environment of a seed: the registers, the two spilled pointers, and the image atoms *)
Lemma s4_E_facts : forall (regs1 : bvmap 5 word) (vp vc : Z),
  (forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s4_E regs1 vp vc) n = getr regs1 r) /\
  ew (s4_E regs1 vp vc) 32 = Z_to_bv 64 vp /\ ew (s4_E regs1 vp vc) 33 = Z_to_bv 64 vc /\
  img_env VAL A_LIM (s4_E regs1 vp vc) /\ env_agree 32 (Ereg regs1 (map (Z_to_bv 64) [vp; vc])) (s4_E regs1 vp vc).
Proof.
intros regs1 vp vc. split; [|split; [|split; [|split]]].
- intros n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  unfold s4_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
- unfold s4_E. change 32%nat with (32 + 0)%nat. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs1 _ 0). reflexivity.
- unfold s4_E. change 33%nat with (32 + 1)%nat. rewrite Eimg_low by (unfold A_TEXT; lia).
  rewrite (ew_Ereg_extra regs1 _ 1). reflexivity.
- unfold s4_E. apply Eimg_env.
- split; [intros n Hn; unfold s4_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation RLO := CMD_RLO.
#[local] Notation RHI := CMD_RHI.
Hypothesis HB : CmdBSyms B.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis PRW : prog_rw SEGS B.
Hypothesis IMG : cmd_img_facts SEGS B.
Let cif_prog_img : forall a, inFP cmd_PG a -> in_img SEGS a :=
  CmdRecBase.cif_prog_img _ _ IMG.
Let cmd_heap_tail_vis : forall ly S (W : world SEGS) mem md p n e, AR SEGS B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= e < p + req_size n -> atail_vis SEGS W mem e :=
  CmdRecImg.cmd_heap_tail_vis SEGS B LAWS HB.

(* the slot's 56 bytes are addressable at every AR state: they lie in a zero-shadow range of the record *)
Lemma s4_slot_ra : forall c ly S (W : world SEGS) mem md,
  AR SEGS B ly S W mem md -> s4_cok c -> range_addressable (rdW W mem) SHADOW_OFF c 56.
Proof using fx rc SK PI HB LAWS.
intros c ly S W mem md HAR Hc. destruct Hc as [[H1 H2] | ->].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0xada00, 0x5e3b00 - 0xada00));
  [exact HAR | vm_compute; tauto | reflexivity | reflexivity | cbn [fst]; unfold A_G_REC, OFF_CALLS in H1; lia
  | cbn [fst snd]; unfold A_G_REC, OFF_ANSWER in H2; lia].
- apply (cmd_addressable_in SEGS B LAWS HB ly S W mem md (0x5e3be0, 0x5e3c18 - 0x5e3be0));
  [exact HAR | vm_compute; tauto | reflexivity | reflexivity | cbn [fst]; unfold A_REC_SPILL; lia
  | cbn [fst snd]; unfold A_REC_SPILL; lia].
Qed.
(* the seed: the symbolic state at a program point of the stage, and its shadow entry *)
Lemma s4_seed : forall (ph : nat) (nv : Z) ly S (W : world SEGS) mem md (regs1 : bvmap 5 word) (pcz s1 c vp vc : Z),
  AR SEGS B ly S W mem md ->
  getr regs1 2 = w64 s1 -> getr regs1 9 = w64 s1 -> getr regs1 20 = w64 SHADOW_OFF ->
  getr regs1 22 = w64 c -> getr regs1 23 = w64 (c + 4) -> getr regs1 24 = w64 (c + 8) ->
  getr regs1 27 = w64 (SHADOW_OFF + (c + 4) / 8) ->
  2 ^ 46 <= s1 -> s1 + 64 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  s4_cok c -> c mod 8 = 0 ->
  0 <= nv < 2 ^ 32 -> 0 <= vp < 2 ^ 64 -> 0 <= vc < 2 ^ 64 ->
  aval_mem (rdW W mem) (s1 + 16) 8 vc -> aval_mem (rdW W mem) (s1 + 24) 8 vp ->
  (ph <> 0%nat -> aval_mem (rdW W mem) (c + 4) 4 nv) ->
  st_ok_pi SEGS VAL (s4_E regs1 vp vc) (s4_ss pcz (s4_rs ph nv))
    (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + pcz)) mem (seg_rom SEGS)))
  /\ sh_ok SEGS s4_Bx s4_SH (s4_E regs1 vp vc) (mrestrict (w_H W) mem).
Proof using fx rc SK PI HB LAWS PRW cmd_heap_tail_vis.
intros ph nv ly S W mem md regs1 pcz s1 c vp vc HAR R2 R9 R20 R22 R23 R24 R27
  Hs1lo Hs1hi Hs1a Hc Hc8 Hnv Hvp Hvc Hv16 Hv24 Hv4.
pose proof (s4_c_range c Hc) as (Hc1 & Hc2 & Hc3).
set (E := s4_E regs1 vp vc).
destruct (s4_E_facts regs1 vp vc) as (EE & E32 & E33 & HEI & _). fold E in EE, E32, E33, HEI.
assert (E2 : ew E 2 = Z_to_bv 64 s1) by (rewrite (EE 2%nat (2%bv : bv 5) eq_refl); exact R2).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (20%bv : bv 5) eq_refl); exact R20).
assert (E22 : ew E 22 = Z_to_bv 64 c) by (rewrite (EE 22%nat (22%bv : bv 5) eq_refl); exact R22).
assert (U2 : bv_unsigned (ew E 2) = s1) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF) by (rewrite E20; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = c) by (rewrite E22; apply unsigned_lit_small; lia).
assert (HWR : forall o, 0 <= o < 56 -> writable_at SEGS (mrestrict (w_H W) mem) (c + o)).
{ intros o Ho. apply PRW. apply (sa_HPROG B HB LAWS).
  exact (proj2 (s4_in_rec c (c + o) Hc ltac:(lia))). }
assert (RSP : region_ok SEGS E (mrestrict (w_H W) mem) s4_spill).
{ unfold s4_spill, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U2. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  constructor; [|constructor; [|constructor]].
  - apply (chunk_ok_val SEGS E _ s1 16 8 (SOff 33 0) vc);
    [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    apply s4_val_of_aval. exact Hv16.
  - apply (chunk_ok_val SEGS E _ s1 24 8 (SOff 32 0) vp);
    [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
    apply s4_val_of_aval. exact Hv24. }
assert (RNA : ph <> 0%nat -> region_ok SEGS E (mrestrict (w_H W) mem) (s4_nargs nv)).
{ intros Hph. unfold s4_nargs, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U22. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply HWR; lia|].
  constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ c 4 4 (SLit nv) nv);
  [cbn [sv_denot]; reflexivity | cbn; lia | cbn; lia |].
  apply s4_val_of_aval. exact (Hv4 Hph). }
assert (RAR : forall j, 0 <= j <= 5 -> region_ok SEGS E (mrestrict (w_H W) mem) (s4_args j)).
{ intros j Hj. unfold s4_args, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U22. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply HWR; lia|]. constructor. }
assert (HFACTS : facts_ok E s4_facts).
{ unfold facts_ok, s4_facts. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
  split; [|split; [exact I | exact I]].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2, U20, U22.
  rewrite SB_SHADOW_OFF. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  change (2 ^ 3) with 8. unfold A_G_REC, OFF_CALLS, A_REC_SPILL.
  split; [repeat split; lia|]. split; [repeat split; lia|]. split; [repeat split; lia | exact I]. }
assert (HSH : sh_ok SEGS s4_Bx s4_SH E (mrestrict (w_H W) mem)).
{ unfold sh_ok, s4_SH. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E s4_Bx 22 c 56 c 0 56);
  [ exact (s4_slot_ra c ly S W mem md HAR Hc)
  | unfold s4_Bx; rewrite U_SOff, U20, Z.add_0_r; apply zcanon_id; unfold M64, SHADOW_OFF; lia
  | rewrite U_SOff, U22, Z.add_0_r; apply zcanon_id; unfold M64; lia
  | lia | lia | intros x Hx; cbn [Z.min Z.max] in Hx; unfold SHADOW_OFF; lia ]. }
split; [|exact HSH].
unfold s4_ss. apply pa_entry_st_ok_full.
- apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
  repeat (destruct Hr as [<- | Hr];
  [ lazymatch goal with |- getr _ _ = sv_denot _ (sr_get ?a ?rr2) =>
      let v := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with v end;
    first
    [ rewrite (denot_shx E 22%nat 20%nat 4 c SHADOW_OFF E22 E20) by (unfold SHADOW_OFF; lia); exact R27
    | cbn [sv_denot];
      first
      [ rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
        first [ symmetry; apply EE; reflexivity
              | rewrite (EE 2%nat (2%bv : bv 5) eq_refl), R2; exact R9 ]
      | rewrite (EE 22%nat (22%bv : bv 5) eq_refl), R22, unsigned_lit_small by lia;
        first [ exact R23 | exact R24 ]
      | apply getr_zero ] ]
  | ]); try (destruct Hr; fail).
- destruct ph as [|[|ph]]; vm_compute; reflexivity.
- destruct ph as [|[|ph]]; cbn [s4_rs];
  repeat apply Forall_cons; try apply Forall_nil;
  first [ exact RSP | apply RNA; discriminate | apply RAR; lia ].
- apply pairwise_disjoint_of_extents.
  destruct ph as [|[|ph]]; cbn [s4_rs];
  unfold s4_spill, s4_nargs, s4_args, extent_of_region;
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite ?U2, ?U22; cbn [zpairwise_disjoint zall_disjoint]; unfold zdisj; cbn [fst snd];
  repeat split; lia.
- exact HFACTS.
Qed.
Lemma s4_awr_slot : forall c (O : list (Z * Z)) STK sp0 bl0 blc fr0 ly own a,
  s4_cok c -> c <= a < c + 56 -> awr_byte SEGS B STK sp0 (sa_FP O) bl0 blc fr0 ly own a.
Proof using fx rc SK PI HB LAWS cif_prog_img cmd_heap_tail_vis.
intros c O STK sp0 bl0 blc fr0 ly own a Hc Ha.
destruct (s4_in_rec c a Hc Ha) as [_ HPG].
right. right. right. right. left.
split; [exact (s4_inFP c O a Hc Ha)|].
split; [exact (sa_HPROG B HB LAWS a HPG) | exact (cif_prog_img a HPG)].
Qed.

(* ---- the mid-state of the stage ---- *)
(* the M2 shape with the recorded arguments, the recorder's blocks and the spent budget as parameters: the three
   runs and the two calls of the stage all keep it. Oj is the list the recorder owns, Ok the list the block
   accounting owns; they differ between the return of a call and the store of the copy that call made. *)
Definition s4_mid ly S (W : world SEGS) (regs : bvmap 5 word) mem md (R : rstate) (O : list (Z * Z))
  lyc Sc (Wc : world SEGS) (regs1 : bvmap 5 word) memc mdc (pos : Z)
  (args : list (list byte)) (Oj Ok : list (Z * Z)) (ev acc live : Z) : Prop :=
let c := sa_c R in
sa_core B ly S W regs mem md O lyc Sc Wc regs1 memc mdc ev pos /\
getr regs1 20 = w64 SHADOW_OFF /\ getr regs1 22 = w64 c /\ getr regs1 23 = w64 (c + 4) /\
getr regs1 24 = w64 (c + 8) /\ getr regs1 27 = w64 (SHADOW_OFF + (c + 4) / 8) /\
sa_buf0 (rdW Wc memc) (frame_addr lyc 1 pos) /\
rec_repA B lyc Sc (rdW Wc memc) (rec_record R REC_ADD args) Oj /\
(forall pn, In pn Oj -> In pn Ok) /\
sa_acct B ly S R O lyc Sc Ok live /\
mo_le MT S Sc acc.
(* the block xstrdup made for the argument it just copied *)
Definition s4_fresh (ly1 : alayout) (S1 : astate) (rd : reader) (Oj : list (Z * Z)) (p n : Z) (s : list byte) : Prop :=
In (p, n) (ablocks B ly1 S1) /\ 4096 <= p /\ n = Z.of_nat (length s) + 1 /\ Z.of_nat (length s) <= LMAX /\
astr_atR rd p s /\ ~ In p (map fst Oj) /\ iv_apart p n A_G_REC REC_SIZE /\ iv_apart p n A_REC_SPILL SC_SIZE.

Lemma s4_mid_of_M2 : forall ly S W regs mem md R O uri id lyc Sc Wc regs1 memc mdc pos,
  sa_M2m B MT ly S W regs mem md R O uri id lyc Sc Wc regs1 memc mdc pos ->
  exists O2, s4_mid ly S W regs mem md R O lyc Sc Wc regs1 memc mdc pos
    [sarg uri; dec id] O2 O2 (sa_ev2 R) (sa_acc2 MT R uri id) (sa_live2 uri id).
Proof using fx rc SK PI.
intros ly S W regs mem md R O uri id lyc Sc Wc regs1 memc mdc pos
  (HC & H20 & H22 & H23 & H24 & H27 & HBUF & O2 & HREP & HACCT & HMLE).
exists O2. unfold s4_mid.
split; [exact HC|]. split; [exact H20|]. split; [exact H22|]. split; [exact H23|].
split; [exact H24|]. split; [exact H27|]. split; [exact HBUF|]. split; [exact HREP|].
split; [intros pn Hpn; exact Hpn|]. split; [exact HACCT | exact HMLE].
Qed.
Lemma s4_M3_of_mid : forall ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos O3,
  s4_mid ly S W regs mem md R O lyc Sc Wc regs1 memc mdc pos (sa_A uri id placement client) O3 O3
    (sa_ev3 R) (sa_acc3 MT R uri id placement client) (sa_live3 uri id placement client) ->
  sa_M3m B MT ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos.
Proof using fx rc SK PI.
intros ly S W regs mem md R O uri id placement client lyc Sc Wc regs1 memc mdc pos O3
  (HC & H20 & H22 & H23 & H24 & H27 & HBUF & HREP & HSUB & HACCT & HMLE).
unfold sa_M3m. split; [exact HC|]. split; [exact H22|]. split; [exact HBUF|].
exists O3. split; [exact HREP|]. split; [exact HACCT | exact HMLE].
Qed.
Lemma s4_acct_step : forall ly S R O lyc Sc Ok live ly1 S1 p n,
  sa_acct B ly S R O lyc Sc Ok live ->
  Permutation (ablocks B ly1 S1) ((p, n) :: ablocks B lyc Sc) ->
  Forall (fun qk => iv_apart p n (fst qk) (snd qk)) (ablocks B lyc Sc) -> 1 <= n ->
  sa_acct B ly S R O ly1 S1 (Ok ++ [(p, n)]) (live + n).
Proof using fx rc SK PI.
intros ly S R O lyc Sc Ok live ly1 S1 p n (A1 & A2 & A3 & A4 & A5) HP HF Hn.
assert (Hin1 : forall pn, In pn (ablocks B lyc Sc) -> In pn (ablocks B ly1 S1))
  by (intros pn Hpn; eapply Permutation_in; [apply Permutation_sym; exact HP | right; exact Hpn]).
assert (Hnew : In (p, n) (ablocks B ly1 S1))
  by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
split; [|split; [|split; [|split]]].
- intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [exact (A1 pn Hpn)|].
  cbn [In] in Hpn. destruct Hpn as [Hpn | []]. subst pn.
  destruct (in_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec)) (p, n) O) as [Hi | Hi];
  [left; exact Hi | right].
  intros Hin. pose proof (A3 (p, n) Hin Hi) as Hc.
  pose proof (proj1 (Forall_forall _ _) HF (p, n) Hc) as Hap. unfold iv_apart in Hap. cbn [fst snd] in Hap. lia.
- intros pn Hpn. eapply Permutation_in in Hpn; [|exact HP]. cbn [In] in Hpn. destruct Hpn as [Hpn | Hpn].
  + subst pn. right. apply in_or_app. right. left. reflexivity.
  + destruct (A2 pn Hpn) as [Hk | Hk]; [left; exact Hk | right; apply in_or_app; left; exact Hk].
- intros pn Hpn Hno. apply Hin1. exact (A3 pn Hpn Hno).
- intros pn Hpn. apply in_app_or in Hpn as [Hpn | Hpn]; [apply Hin1; exact (A4 pn Hpn)|].
  cbn [In] in Hpn. destruct Hpn as [Hpn | []]. subst pn. exact Hnew.
- rewrite (blocks_bytes_bsum B ly1 S1), (bsum_perm _ _ HP), bsum_cons. cbn [snd].
  rewrite (blocks_bytes_bsum B lyc Sc) in A5. lia.
Qed.

(* ---- the memory and the registers of the mid-state, kept by a run that writes only inside the slot ---- *)
(* sa_core and the frame's buffer shadow, when every byte outside the slot [c, c + 56) and the kept registers stay *)
Lemma s4_core_kept : forall ly S W regs mem md O lyc Sc Wc regsA memA mdA regsB memB mdB ev pos c,
  sa_core B ly S W regs mem md O lyc Sc Wc regsA memA mdA ev pos ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memB mdB ev ->
  s4_cok c ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (c <= a < c + 56) -> rdW Wc memB a = rdW Wc memA a) ->
  (forall z, In z s4_kz -> getr regsB (Z_to_bv 5 z) = getr regsA (Z_to_bv 5 z)) ->
  sa_core B ly S W regs mem md O lyc Sc Wc regsB memB mdB ev pos /\
  (sa_buf0 (rdW Wc memA) (frame_addr lyc 1 pos) -> sa_buf0 (rdW Wc memB) (frame_addr lyc 1 pos)).
Proof using fx rc SK PI LAWS.
intros ly S W regs mem md O lyc Sc Wc regsA memA mdA regsB memB mdB ev pos c HC HJB Hc KM KR.
unfold sa_core in HC |- *. cbv zeta in HC |- *.
destruct HC as (HJ & HFRAME & Hs16 & Hs24 & Hs48 & HFLAG & A2 & A3 & A4 & A8 & A9 & A18 & A19 & A21 & A25 & A26).
pose proof (s4_c_range c Hc) as (Hc1 & Hc2 & Hc3).
pose proof asan_consts as (C1 & _).
pose proof HJ as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
assert (HSTKa : 176 <= SUP_ADD_STK) by (vm_compute; discriminate).
pose proof (s4_s1_facts (spZ regs) Hal16) as Hs1v.
assert (Hin1pos : In (1, pos) (frames Sc)) by (rewrite Hfrsc; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc Wc memA mdA 1 pos HARc Hin1pos) as (HF4096 & HFceil & _).
pose proof (frm_off_imgP B lyc Sc Wc memA mdA 1 pos HARc Hin1pos) as HFoff.
assert (HFB : fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
rewrite HFB in HFceil, HFoff. unfold off_img in HFoff.
assert (KS : forall a, sa_s1 (spZ regs) <= a < spZ regs -> rdW Wc memB a = rdW Wc memA a)
  by (intros a Ha; apply KM; lia).
split.
- split; [exact HJB|].
  split; [intros j r Hj; apply (s4_aval_kept _ _ _ 8 _ (HFRAME j r Hj));
          assert (Hjlt : (j < 13)%nat) by (apply (proj1 (nth_error_Some sa_saved j)); rewrite Hj; discriminate);
          intros x Hx; apply KS; lia|].
  split; [apply (s4_aval_kept _ _ _ 8 _ Hs16); intros x Hx; apply KS; lia|].
  split; [apply (s4_aval_kept _ _ _ 8 _ Hs24); intros x Hx; apply KS; lia|].
  split; [apply (s4_aval_kept _ _ _ 8 _ Hs48); intros x Hx; apply KS; lia|].
  split; [unfold rdword in HFLAG |- *; rewrite HFB in HFLAG |- *; rewrite !KM by lia; exact HFLAG|].
  split; [s4_kr KR A2 2|]. split; [s4_kr KR A3 3|]. split; [s4_kr KR A4 4|].
  split; [s4_kr KR A8 8|]. split; [s4_kr KR A9 9|]. split; [s4_kr KR A18 18|].
  split; [s4_kr KR A19 19|]. split; [s4_kr KR A21 21|]. split; [s4_kr KR A25 25|].
  s4_kr KR A26 26.
- intros HBUF i Hi. rewrite KM; [exact (HBUF i Hi) | |];
  pose proof (Z.div_pos (frame_addr lyc 1 pos) 8 ltac:(lia) ltac:(lia)); unfold SHADOW_OFF;
  [split; [lia|]; assert (frame_addr lyc 1 pos / 8 < 2 ^ 47) by (apply Z.div_lt_upper_bound; lia); lia | lia].
Qed.
(* the recorder's blocks lie in [4096, alloc_ceiling) and apart from g_rec and record.spill *)
Lemma s4_blk_range : forall lyc Sc (Wc : world SEGS) memc mdc rd R (Oj : list (Z * Z)) p0 n0 i,
  AR SEGS B lyc Sc Wc memc mdc -> rec_repA B lyc Sc rd R Oj -> In (p0, n0) Oj -> 0 <= i < n0 ->
  0 <= p0 + i < 2 ^ 64 /\ ~ (0x5e3740 <= p0 + i < 0x5e3c18).
Proof using fx rc SK PI HB LAWS cmd_heap_tail_vis.
intros lyc Sc Wc memc mdc rd R Oj p0 n0 i HAR HREP Hin Hi.
destruct (rec_repA_fields B HB LAWS lyc Sc rd R Oj HREP)
  as (_ & _ & _ & _ & _ & _ & _ & _ & Hsz).
destruct (Hsz (p0, n0) Hin) as (Hbl & Hn1 & _). cbn [fst snd] in Hn1.
destruct (al_blocks SEGS B LAWS lyc Sc Wc memc mdc p0 n0 HAR Hbl) as (_ & H4096 & Hpc & _).
pose proof (blk_off_imgP B lyc Sc Wc memc mdc p0 n0 HAR Hbl) as Hoff. unfold off_img in Hoff.
pose proof (req_size_pos n0 ltac:(lia)) as [_ Hrq]. pose proof asan_consts as (C1 & _).
split; lia.
Qed.
(* the whole mid-state, when every byte and the kept registers stay *)
Lemma s4_mid_kept : forall ly S W regs mem md R O lyc Sc Wc regsA memA mdA regsB memB mdB pos args Oj Ok ev acc live,
  s4_mid ly S W regs mem md R O lyc Sc Wc regsA memA mdA pos args Oj Ok ev acc live ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memB mdB ev ->
  (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memB a = rdW Wc memA a) ->
  (forall z, In z s4_kz -> getr regsB (Z_to_bv 5 z) = getr regsA (Z_to_bv 5 z)) ->
  s4_mid ly S W regs mem md R O lyc Sc Wc regsB memB mdB pos args Oj Ok ev acc live.
Proof using fx rc SK PI HB LAWS cmd_heap_tail_vis.
intros ly S W regs mem md R O lyc Sc Wc regsA memA mdA regsB memB mdB pos args Oj Ok ev acc live
  (HC & H20 & H22 & H23 & H24 & H27 & HBUF & HREP & HSUB & HACCT & HMLE) HJB KM KR.
pose proof (s4_c_of_R R) as [Hc _].
pose proof (proj1 HC) as HJ. pose proof (proj1 HJ) as HARc.
destruct (s4_core_kept ly S W regs mem md O lyc Sc Wc regsA memA mdA regsB memB mdB ev pos (sa_c R) HC HJB Hc
  (fun a Ha _ => KM a Ha) KR) as [HC' HB'].
unfold s4_mid. split; [exact HC'|].
split; [s4_kr KR H20 20|]. split; [s4_kr KR H22 22|]. split; [s4_kr KR H23 23|].
split; [s4_kr KR H24 24|]. split; [s4_kr KR H27 27|].
split; [exact (HB' HBUF)|].
split.
- apply (rec_repA_kept B HB LAWS lyc Sc (rdW Wc memA) lyc Sc (rdW Wc memB) _ Oj HREP).
  + intros a Ha. pose proof (s4_in_rec_range a Ha). apply KM. lia.
  + intros p0 n0 i Hin Hi.
    destruct (s4_blk_range lyc Sc Wc memA mdA _ _ Oj p0 n0 i HARc HREP Hin Hi) as [Hr _]. exact (KM _ Hr).
  + intros pn Hpn. destruct (rec_repA_fields B HB LAWS lyc Sc (rdW Wc memA) _ Oj HREP)
      as (_ & _ & _ & _ & _ & _ & _ & _ & Hsz).
    exact (proj1 (Hsz pn Hpn)).
- split; [exact HSUB|]. split; [exact HACCT | exact HMLE].
Qed.
(* the store of a copy: nargs := k + 1 and args[k] := p, the copy xstrdup made, joins the recorder *)
Lemma s4_store : forall ly S W regs mem md R O lyc Sc Wc regsA memA mdA regsB memB mdB pos args Oj ev acc live p n s,
  s4_mid ly S W regs mem md R O lyc Sc Wc regsA memA mdA pos args Oj (Oj ++ [(p, n)]) ev acc live ->
  s4_fresh lyc Sc (rdW Wc memA) Oj p n s ->
  (length args < 6)%nat ->
  ajournal SEGS B SUP_ADD_STK (spZ regs) (sa_FP O) ly S W mem md [(1, pos)] lyc Sc Wc memB mdB ev ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (sa_c R + 4 <= a < sa_c R + 8) ->
     ~ (sa_c R + 8 + 8 * Z.of_nat (length args) <= a < sa_c R + 16 + 8 * Z.of_nat (length args)) ->
     rdW Wc memB a = rdW Wc memA a) ->
  aval_mem (rdW Wc memB) (sa_c R + 4) 4 (Z.of_nat (length args) + 1) ->
  aval_mem (rdW Wc memB) (sa_c R + 8 + 8 * Z.of_nat (length args)) 8 p ->
  (forall z, In z s4_kz -> getr regsB (Z_to_bv 5 z) = getr regsA (Z_to_bv 5 z)) ->
  s4_mid ly S W regs mem md R O lyc Sc Wc regsB memB mdB pos (args ++ [s]) (Oj ++ [(p, n)]) (Oj ++ [(p, n)])
    ev acc live.
Proof using fx rc SK PI HB LAWS cmd_heap_tail_vis.
intros ly S W regs mem md R O lyc Sc Wc regsA memA mdA regsB memB mdB pos args Oj ev acc live p n s
  (HC & H20 & H22 & H23 & H24 & H27 & HBUF & HREP & HSUB & HACCT & HMLE)
  (Hnew & Hp4096 & Hn & HLs & Hstr & Hfr & Hap1 & Hap2) Hlen HJB KM Hna Harg KR.
pose proof (s4_c_of_R R) as [Hc _]. pose proof (s4_c_range (sa_c R) Hc) as (Hc1 & Hc2 & Hc3).
pose proof (proj1 HC) as HJ. pose proof (proj1 HJ) as HARc.
assert (Hk6 : Z.of_nat (length args) <= 5) by lia.
destruct (s4_core_kept ly S W regs mem md O lyc Sc Wc regsA memA mdA regsB memB mdB ev pos (sa_c R) HC HJB Hc
  (fun a Ha Hn' => KM a Ha ltac:(lia) ltac:(lia)) KR) as [HC' HB'].
unfold s4_mid. split; [exact HC'|].
split; [s4_kr KR H20 20|]. split; [s4_kr KR H22 22|]. split; [s4_kr KR H23 23|].
split; [s4_kr KR H24 24|]. split; [s4_kr KR H27 27|].
split; [exact (HB' HBUF)|].
split.
- destruct (rec_repA_fields B HB LAWS lyc Sc (rdW Wc memA) _ Oj HREP)
    as (_ & _ & _ & _ & _ & _ & _ & _ & Hsz).
  destruct (al_blocks SEGS B LAWS lyc Sc Wc memA mdA p n HARc Hnew) as (_ & _ & Hpc & _).
  pose proof (blk_off_imgP B lyc Sc Wc memA mdA p n HARc Hnew) as Hoff. unfold off_img in Hoff.
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. pose proof asan_consts as (C1 & _).
  apply (rec_repA_append B HB LAWS lyc Sc (rdW Wc memA) lyc Sc (rdW Wc memB) R args Oj s p n
    HREP Hlen).
  + intros a Ha H1 H2. pose proof (s4_in_rec_range a Ha). unfold CALL_OFF_NARGS, CALL_OFF_ARGS in H1, H2.
    apply KM; lia.
  + intros p0 n0 i Hin Hi.
    destruct (s4_blk_range lyc Sc Wc memA mdA _ _ Oj p0 n0 i HARc HREP Hin Hi) as [Hr Hno].
    apply KM; [exact Hr | lia | lia].
  + intros pn Hpn. exact (proj1 (Hsz pn Hpn)).
  + unfold CALL_OFF_NARGS. exact Hna.
  + unfold CALL_OFF_ARGS. exact Harg.
  + exact Hnew.
  + lia.
  + exact Hn.
  + exact HLs.
  + apply (lem_astr_keep (rdW Wc memA) (rdW Wc memB) p s Hstr).
    intros i Hi. apply KM; lia.
  + exact Hfr.
  + exact Hap1.
  + exact Hap2.
- split; [intros pn Hpn; exact Hpn|].
  split; [exact HACCT | exact HMLE].
Qed.
(* the kept registers of a run: the same symbolic value before and after, under the same environment *)
Lemma s4_regs_eq : forall E (sr1 sr2 : list sv) (regsA regsB : bvmap 5 word),
  (forall r, getr regsA r = sv_denot E (sr_get sr1 r)) ->
  (forall r, getr regsB r = sv_denot E (sr_get sr2 r)) ->
  forallb (fun z => sv_eqb (sr_get sr2 (Z_to_bv 5 z)) (sr_get sr1 (Z_to_bv 5 z))) s4_kz = true ->
  forall z, In z s4_kz -> getr regsB (Z_to_bv 5 z) = getr regsA (Z_to_bv 5 z).
Proof using.
intros E sr1 sr2 regsA regsB HA HB' Hb z Hz. rewrite HA, HB'.
pose proof (proj1 (forallb_forall _ _) Hb z Hz) as Hz'. cbv beta in Hz'. apply sv_eqb_eq in Hz'. rewrite Hz'.
reflexivity.
Qed.
End e.
End f.
End d.
(* the windows of a run's regions, all over atom 22 (U22 : bv_unsigned (ew E 22) = c), lie in the set the goal names *)
Ltac s4_kof U22 :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a := fresh "a" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in
  intros b wlo whi a Hin Hrr; vm_compute in Hin;
  repeat (let Hq := fresh "Hq" in
          destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U22 in Hrr; lia|]);
  destruct Hin.
