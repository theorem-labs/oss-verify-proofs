(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, pinned 5ac5ce0954f8), segment S6 (0x8110c-0x81144,
   fs.c:328-333): the six PROGRAM calls
     live = fuzz_alloc_live (); fuzz_alloc_peak_reset (); body = preset_base64_decode (text, &len);
     peak = fuzz_alloc_peak (); check_bounded_alloc (peak - live, n); check_as_written (text, body, len)
   from the boundary after the text copy (lib/B/FSW_entry_defs.v INV_C5, fe_ss PC_C5 = 0x8110c) to the boundary after
   check_as_written returns (INV_C6, fe_ss RA_caw = 0x81148). One step per call (B call sites 0x8110c, 0x81114, 0x81120,
   0x81128, 0x81134, 0x81144; the B listing has A's instruction sequence here, `addi s4, s8, 32` at 0x81108 before the
   first call), each in the recipe of lib/B/FSW_entry_s6a.v (s6_fpreU at the call, the callee's CTX-free spec of
   lib/B/FSH_Fn_*.v, s6_resume on the return). The decoder's refusal arm (cnt = g_fail_at) is dead on the walk: fs_stat
   pins g_fail_at = SIZE_MAX and the entry's count room keeps g_count under 2^63. The decoded block's size bound
   (b64_dec_bound) makes check_bounded_alloc's premise `peak - live <= b64_alloc_bound n` hold, since the peak after the
   reset is live + dec_size and dec_size tb = |tb| / 4 * 3 + 3 = b64_alloc_bound |tb| with |tb| = fe_n. Each callee's
   stack bound (STK_preset_base64_decode, STK_check_bounded_alloc, STK_check_as_written of lib/B/FSH_Base.v, from B's
   callee frames) is checked + 112 within LLVMF_STK by vm_compute over the definitions at its call, never stated as a
   value. decode_spec_ff's `range_addressable ... lenp 8` premise (lenp =
   frame + 32) comes from `len`'s shadow byte (fe_SF + 4) being 0 since `sb zero, 4(s9)` at 0x8109c: INV_C5's last
   conjunct fe_lensh, carried in INV6_1 / INV6_2 across fuzz_alloc_live and fuzz_alloc_peak_reset (each run starts
   from fe_ss_z, the canonical state with that byte as a shadow chunk, and the callee's journal keeps the frame's
   shadow), then FSW_entry_canon.v fe_lensh_ra at the decode call. The decoder's bad-text arm returns the block list
   EQUAL to the caller's (the base's post), used here as a permutation.
   rule 24: proves function LLVMFuzzerTestOneInput (segment S6; reuse search: proof-index LLVMFuzzerTestOneInput,
   ported from a working branch 08ad70da3bf).
   Ported from: a working branch 0d34d65d2b7 lib/A/FSW_entry_s6.v (fs.asan 0x8108c-0x810c4), with the CTX
   premises dropped (decode_spec_ff / check_as_written_spec of the base are CTX-free; s6_chain has no trace conjunct),
   the fe_lensh layer of a working branch 60372e5bd05 (lib/A/FSW_entry_{defs,canon}.v) added, and
   every address image B's own.
   RELOC-B hypotheses: none (the six callee specs are FsEntryFns fields of lib/B/FSH_Fn_entry.v). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0s YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame FSW_K3 FSW_strkit.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn FSH_Harness FSH_Fn_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSH_Fn_alloc FSH_Fn_checks FSH_Fn_writer.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterSpecFacts.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSW_entry_defs FSW_entry_canon FSW_entry_ar FSW_entry_s6a.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.


Section s6. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis en_alloc_live : @fuzz_alloc_live_spec fx rc SK tfibsegs B.
Hypothesis en_alloc_peak_reset : @fuzz_alloc_peak_reset_spec fx rc SK tfibsegs B.
Hypothesis en_decode : @decode_spec_ff fx rc SK B tfibsegs.
Hypothesis en_alloc_peak : @fuzz_alloc_peak_spec fx rc SK tfibsegs B.
Hypothesis en_bounded_alloc : @check_bounded_alloc_spec fx rc SK tfibsegs B.
Hypothesis en_as_written : @check_as_written_spec fx rc SK tfibsegs B.

(* the registers the segment carries: s3 = n, s4 = &len, s5 = text, besides the canonical ones *)
Definition S6_regs (cx : fecx) (E : env) (text : Z) : Prop :=
  fe_regs_core cx E /\ fe_n cx <= 3 * 2 ^ 20 /\
  ew E 19 = Z_to_bv 64 (fe_n cx) /\ ew E 20 = Z_to_bv 64 (fe_F cx + 32) /\ ew E 21 = Z_to_bv 64 text.

(* (D1) 0x81110, fuzz_alloc_live returned: a0 = g_live; `len`'s shadow byte still 0 (fe_lensh, for decode) *)
Definition INV6_1 : fe_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text,
  U3 = [] /\ Permutation (ablocks B ly3 S3) ((text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) /\
  fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1) /\ S6_regs cx E text /\
  ew E 10 = Z_to_bv 64 (c_live cx) /\
  cstr_ok tfibsegs W3 (ms_mem ms3) text (fe_tb cx) /\
  fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx + 3) /\ fe_lensh cx W3 (ms_mem ms3).

(* (D2) 0x81118, fuzz_alloc_peak_reset returned: s7 = g_live and g_peak = g_live; fe_lensh as at D1 *)
Definition INV6_2 : fe_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text,
  U3 = [] /\ Permutation (ablocks B ly3 S3) ((text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) /\
  fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1) /\ S6_regs cx E text /\
  ew E 23 = Z_to_bv 64 (c_live cx) /\
  cstr_ok tfibsegs W3 (ms_mem ms3) text (fe_tb cx) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (c_live cx) (c_live cx) (c_cnt cx + 3) SIZE_MAXZ /\ fe_lensh cx W3 (ms_mem ms3).

(* the decoder's answer in the form the walk carries it: the bytes and the block, from which caw_answerA is
   rebuilt at every later state (s6_answer) *)
Definition S6_ans (cx : fecx) ly3 S3 U3 (W3 : world tfibsegs) (ms3 : machine_state) (body l : Z) : Prop :=
  (WriterSpec.b64_dec (fe_tb cx) = None /\ body = 0 /\ l = SIZE_MAXZ) \/
  (exists bs, WriterSpec.b64_dec (fe_tb cx) = Some bs /\ body <> 0 /\ l = Z.of_nat (length bs) /\
     body mod 16 = 0 /\ 4096 + HEAD <= body /\
     zbytes_at tfibsegs W3 (ms_mem ms3) body bs /\
     val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) (body - HEAD) 8 (dec_size (fe_tb cx)) /\
     In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly3 S3) /\ In (body - HEAD, HEAD) U3).

(* what every boundary after the decode carries *)
Definition S6_dec (cx : fecx) (E : env) ly3 S3 U3 (W3 : world tfibsegs) (ms3 : machine_state)
  (text body l : Z) : Prop :=
  U3 = fe_body_U body /\
  Permutation (ablocks B ly3 S3) (fe_body_blocks cx body ++ (text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) /\
  S6_ans cx ly3 S3 U3 W3 ms3 body l /\
  (body <> 0 -> text + fe_n cx + 1 <= body - HEAD \/ body + dec_size (fe_tb cx) <= text) /\
  S6_regs cx E text /\ ew E 46 = Z_to_bv 64 l /\ ew E 23 = Z_to_bv 64 (c_live cx) /\
  cstr_ok tfibsegs W3 (ms_mem ms3) text (fe_tb cx) /\
  fs_glob tfibsegs W3 (ms_mem ms3) (fe_live6 cx body) (c_live cx + dec_size (fe_tb cx)) (c_cnt cx + 4) SIZE_MAXZ.

(* (D3) 0x81124, preset_base64_decode returned: a0 = body *)
Definition INV6_3 : fe_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text body l,
  S6_dec cx E ly3 S3 U3 W3 ms3 text body l /\ ew E 10 = Z_to_bv 64 body /\
  fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1 + EV_preset_base64_decode).

(* (D4) 0x8112c, fuzz_alloc_peak returned: s6 = body, a0 = g_peak *)
Definition INV6_4 : fe_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text body l,
  S6_dec cx E ly3 S3 U3 W3 ms3 text body l /\ ew E 22 = Z_to_bv 64 body /\
  ew E 10 = Z_to_bv 64 (c_live cx + dec_size (fe_tb cx)) /\
  fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1 + EV_preset_base64_decode).

(* (D5) 0x81138, check_bounded_alloc returned *)
Definition INV6_5 : fe_inv := fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text body l,
  S6_dec cx E ly3 S3 U3 W3 ms3 text body l /\ ew E 22 = Z_to_bv 64 body /\
  fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1 + EV_preset_base64_decode).
(* ---- the shared opening of a call step: the entry facts, the frame's geometry, the canonical registers ---- *)
Ltac s6_open HB HINV :=
  let Hgp := fresh "Hgp" in let Htp := fresh "Htp" in let Hra0 := fresh "Hra0" in let Hfr0 := fresh "Hfr0" in
  let Hev := fresh "Hev" in let Hlive := fresh "Hlive" in let Hn0 := fresh "Hn0" in let Htbl := fresh "Htbl" in
  let Hfn0 := fresh "Hfn0" in let Htbo := fresh "Htbo" in let Hstat0 := fresh "Hstat0" in
  let Hc0 := fresh "Hc0" in let Hcnt := fresh "Hcnt" in let Hlv := fresh "Hlv" in
  pose proof (s6_entry B _ HB) as (Hgp & Htp & Hra0 & Hfr0 & Hev & Hlive & Hn0 & Htbl & Hfn0 & Htbo & Hstat0 & Hc0 & Hcnt & Hlv);
  let Hal16 := fresh "Hal16" in let Hceil := fresh "Hceil" in let H47 := fresh "H47" in
  let Hsp1 := fresh "Hsp1" in let Hal1 := fresh "Hal1" in
  pose proof (s6_sp0 B _ HB) as (Hal16 & Hceil & H47 & Hsp1 & Hal1);
  unfold LLVMF_STK in Hceil;
  let C1 := fresh "C1" in let C2 := fresh "C2" in let C3 := fresh "C3" in let C4 := fresh "C4" in
  let C5 := fresh "C5" in pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  let Hlive0 := fresh "Hlive0" in
  lazymatch type of HB with fe_base _ ?cxx =>
    assert (Hlive0 : 0 <= c_live cxx) by (destruct Hstat0 as (pk & _ & _ & _ & _ & Hr); lia) end.

(* the decoder's answer carried to a later state: the block's bytes and its place in the ledger *)
Lemma s6_ans_keep : forall cx ly3 S3 U3 (W3 : world tfibsegs) ms3 ly4 S4 (W4 : world tfibsegs) ms4 body l,
  S6_ans cx ly3 S3 U3 W3 ms3 body l ->
  (body <> 0 -> In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly4 S4)) ->
  (body <> 0 -> forall a, body - HEAD <= a < body + dec_size (fe_tb cx) ->
     mbyte tfibsegs (mrestrict (w_H W4) (ms_mem ms4)) a = mbyte tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) a) ->
  S6_ans cx ly4 S4 U3 W4 ms4 body l.
Proof.
intros cx ly3 S3 U3 W3 ms3 ly4 S4 W4 ms4 body l Hans Hin Hmb.
destruct Hans as [Hl | (bs & Hd & Hne & Hl & H16 & H4096 & Hz & Hv & Hinb & Hu)]; [left; exact Hl|].
pose proof (WriterSpecFacts.b64_dec_bound (fe_tb cx) bs Hd) as Hob. unfold dec_size in *.
right. exists bs. split; [exact Hd|]. split; [exact Hne|]. split; [exact Hl|]. split; [exact H16|].
split; [exact H4096|].
split; [apply (garr8_frame tfibsegs _ _ body bs Hz); intros a Ha; apply Hmb; [exact Hne | unfold HEAD in *; lia]|].
split; [intros j Hj; rewrite (Hmb Hne (body - HEAD + Z.of_nat j) ltac:(unfold HEAD in *; lia)); exact (Hv j Hj)|].
split; [exact (Hin Hne) | exact Hu].
Qed.

(* the answer in the form check_as_written takes *)
Lemma s6_answer : forall cx ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 body l,
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  (forall r, In r U3 -> fst r + snd r <= body \/ body + l <= fst r) ->
  S6_ans cx ly3 S3 U3 W3 ms3 body l ->
  caw_answerA tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) (fe_tb cx) body l.
Proof.
intros cx ly3 S3 U3 W3 ms3 md3 body l HARU Hdis
  [Hl | (bs & Hd & Hne & Hl & H16 & H4096 & Hz & Hv & Hinb & Hu)]; [left; exact Hl|].
pose proof (WriterSpecFacts.b64_dec_bound (fe_tb cx) bs Hd) as Hob.
assert (Hdp : 3 <= dec_size (fe_tb cx)) by (unfold dec_size; Z.div_mod_to_equations; lia).
right. exists bs, (dec_size (fe_tb cx)). split; [exact Hd|]. split; [exact Hne|]. split; [exact Hl|].
split.
{ apply (s6_src_blk B ly3 S3 U3 W3 (ms_mem ms3) md3 (body - HEAD) (dec_size (fe_tb cx) + HEAD) body bs
    HARU Hinb ltac:(unfold HEAD; lia));
  [ intros r Hr; destruct (Hdis r Hr); [left; lia | right; lia]
  | unfold HEAD; lia
  | unfold req_size, dec_size, HEAD in *; destruct (Z.eqb_spec (Z.of_nat (length (fe_tb cx)) / 4 * 3 + 3 + 16) 0);
    lia
  | exact Hz ]. }
split; [split; [exact Hinb|]; split; [exact H16|]; split; [unfold dec_size; lia | exact Hv]|].
split; [unfold dec_size in *; lia | exact Hu].
Qed.

(* `len`'s shadow byte (FSW_entry_defs.v fe_lensh) across a program call of the segment before the decode (U = []):
   the callee's journal keeps the entry frame's shadow outside its footprint (FSW_entry_canon.v fe_lensh_journal) *)
Lemma s6_lensh_call : forall cx ly3 S3 (W3 : world tfibsegs) mem mdc STKc spc FPc ly4 S4 (W4 : world tfibsegs) mem4
  md4 kc,
  ajournal tfibsegs B STKc spc FPc ly3 S3 W3 (unpoison [] mem) mdc [] ly4 S4 W4 (unpoison [] mem4) md4 kc ->
  In (0, c_fpos cx) (frames S3) -> frame_addr ly3 0 (c_fpos cx) = fe_F cx -> ~ inFP FPc (fe_SF cx + 4) ->
  aview tfibsegs (w_H W3) mem (fe_SF cx + 4) = Some 0 -> fe_lensh cx W4 mem4.
Proof.
intros cx ly3 S3 W3 mem mdc STKc spc FPc ly4 S4 W4 mem4 md4 kc HJc Hin EF Hnfp Hz.
rewrite !unpoison_nil in HJc. unfold fe_lensh.
exact (fe_lensh_journal B cx STKc spc FPc ly3 S3 W3 mem mdc [] ly4 S4 W4 mem4 md4 kc HJc Hin EF Hnfp Hz).
Qed.

Lemma s6_step1 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_alloc_live [fe_len_lit (-1)]) INV6_1 ->
  fe_from B FS_PSTAT_FP POST (fe_ss PC_C5 [fe_len_lit (-1)]) (INV_C5 B).
Proof.
intros POST HN cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
s6_open HB HINV.
destruct HINV as (text & HU & Hperm & Hcom & Hcore & Hn3 & E19 & E20 & E21 & E22 & Hcstr & Hstat & Hlsh).
pose proof (s6_walk B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k HB HJ) as (Efrs & Hin & ELY & Etop & EF & EFL).
pose proof (s6_geom B cx ly3 S3 U3 W3 (ms_mem ms3) md3 HARU Hin EF EFL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof Hcore as (A8 & A9 & A2 & A18 & A24 & A25 & A3 & A4 & A26 & A27).
assert (HceilS : alloc_ceiling + LLVMF_STK <= fe_sp0 cx) by (unfold LLVMF_STK; lia).
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite A8; apply wz; lia).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite A24; apply wz; lia).
assert (U25 : bv_unsigned (ew E 25) = fe_SF cx)
  by (rewrite A25; apply wz; unfold kHighShadowEnd in *; lia).
assert (Htxt : In (text, fe_n cx + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
destruct Hstat as (peak & Hglob3).
pose proof HARU as HARU0.
(* the run starts from the canonical state with `len`'s shadow byte as a chunk (fe_ss_z), so its end keeps it *)
pose proof (fe_ss_z_ok cx E _ _ (w_H W3) ms3 HS U25 Hlsh) as HSz. clear HS. rename HSz into HS.
fsw_aj_run_toU entry_tbl_ok HS HJ HARU A_fuzz_alloc_live.
{ apply (fe_awr_z B). exact (s6_awr B cx E ly3 S3 [fe_len_lit (-1)] U8 U24 U25 EF). }
(* ---- at fuzz_alloc_live's entry (0x82eec), ra = 0x81110 ---- *)
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pose proof (fe_lensh_of cx E _ (w_H W3) ms HS ltac:(vm_compute; reflexivity) U25) as Hlsh1.
pose proof (fe_drop_z E _ (w_H W3) ms HS ltac:(vm_compute; reflexivity)) as HSd. clear HS. rename HSd into HS.
pose proof (fe_frame_z E [fe_len_lit (-1)] _ _ HFr) as HFr'. clear HFr. rename HFr' into HFr.
assert (R1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_alloc_live)
  by (apply (fsw_reg_lit (w_H W3) E _ ms 1%bv RA_alloc_live HS);
      [vm_compute; reflexivity | unfold RA_alloc_live; lia]).
assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx)
  by (unfold spZ; rewrite (s6_reg_at E _ ms W3 2%bv 2 HS ltac:(vm_compute; reflexivity)), A2; apply wz; lia).
assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx)
  by (unfold s0Z; rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)), A8; apply wz; lia).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx))
  by (rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact A8).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact A24).
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact A18).
assert (R25 : YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx))
  by (rewrite (s6_reg_at E _ ms W3 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact A25).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = w64 (as_gp B))
  by (rewrite (s6_reg_at E _ ms W3 3%bv 3 HS ltac:(vm_compute; reflexivity)), A3; exact Hgp).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = w64 (as_tp B))
  by (rewrite (s6_reg_at E _ ms W3 4%bv 4 HS ltac:(vm_compute; reflexivity)), A4; exact Htp).
pose proof (s6_frame_at cx E W3 ms _ [fe_len_lit (-1)] HS ltac:(vm_compute; reflexivity) HE U8 U24
  ltac:(lia)) as (Hsv & Hflag & Hcsx).
destruct (s6_sv_words cx E W3 (ms_mem ms) HE Hsv) as (Hw1 & Hw2).
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 8) (raZ (c_regs cx)) HARU ltac:(lia) ltac:(lia) Hw1) as Hw1'.
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 16) (s0Z (c_regs cx)) HARU ltac:(lia) ltac:(lia) Hw2) as Hw2'.
destruct (s6_chain B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ Hw1' Hw2') as (ch & Hch).
assert (HK0 : 0 <= STK_fuzz_alloc) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HKb : STK_fuzz_alloc + 112 <= LLVMF_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hpre : fpreU tfibsegs B STK_fuzz_alloc ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch).
{ apply (s6_fpreU B cx ly3 S3 U3 W3 (ms_mem ms) mdc k (ms_regs ms) STK_fuzz_alloc ch HB HJ HARU
    (s6_arodata B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ HARU) Rsp HK0 HKb);
    [ rewrite R1; apply ret_ok_even; rewrite (wz RA_alloc_live ltac:(unfold RA_alloc_live; lia)); reflexivity
    | unfold raZ; rewrite R1, (wz RA_alloc_live ltac:(unfold RA_alloc_live; lia)); unfold RA_alloc_live; lia
    | exact R3 | exact R4 | rewrite Rsp, Rs0; exact Hch ]. }
assert (Hglob : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) peak (c_cnt cx + 3) SIZE_MAXZ).
{ apply (s6_glob_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hglob3].
  intros a Ha. exact (s6_run_img B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_lit (-1)] a
    HARU0 Hin EF U8 U24 U25 HceilS G6 HFr Ha). }
assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1)
  by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
assert (Hcstr' : cstr_ok tfibsegs W3 (ms_mem ms) text (fe_tb cx)).
{ apply (s6_cstr_carry B ly3 S3 U3 W3 (ms_mem ms) mdc W3 (ms_mem ms3) text (fe_n cx + 1) text (fe_tb cx)
    HARU Htxt ltac:(lia) ltac:(rewrite HU; intros r []) ltac:(lia) ltac:(lia)); [|exact Hcstr].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_lit (-1)] text (fe_n cx + 1)
    (a - text) HARU0 Hin EF Htxt ltac:(lia) U8 U24 U25 HceilS G6 G7 HFr). }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (en_alloc_live ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch (c_live cx) peak (c_cnt cx + 3) SIZE_MAXZ
     Hpre ltac:(rewrite HU; apply s6_heads_nil) Hglob)|].
intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (E10 & Habl & Hglob4 & Hheads4)).
rewrite R1.
(* ---- back at 0x81110 ---- *)
assert (Hlen4 : val_mem tfibsegs (mrestrict (w_H W4) mem4) (fe_F cx + 32) 8 SIZE_MAXZ).
{ intros j Hj.
  rewrite (s6_keep_frame B cx ly3 S3 U3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4
    mem4 md4 0 (fe_F cx + 32 + Z.of_nat j) HARU HJc OK4 PO4 Hin EF ltac:(lia)
    ltac:(intros Hf; exact (inFP_nil _ Hf))).
  apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx) 32 8%N (SLit (-1)) SIZE_MAXZ
    (Forall_inv Hcsx)); [|cbn [Z.of_N]; unfold SIZE_MAXZ; lia|cbn [Z.of_N]; lia|exact Hj].
  apply bv_eq. change (bv_unsigned (sv_denot E (SLit (-1)))) with (U E (SLit (-1))).
  rewrite U_SLit. change (zcanon (-1)) with (2 ^ 64 - 1).
  rewrite (wz SIZE_MAXZ ltac:(unfold SIZE_MAXZ; lia)). reflexivity. }
destruct (s6_resume B cx ly3 S3 U3 W3 (ms_mem ms) mdc k STK_fuzz_alloc [] (ms_regs ms) ly4 S4 U3 W4 regs4 mem4
  md4 0 E [] RA_alloc_live [fe_len_lit (-1)] HB HE HJ HARU HJc OK4 PO4
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) ltac:(intros a _ Hf; exact (inFP_nil a Hf))
  Rsp HK0 HKb Hsv Hflag HP4 R8 R24 R18 R25
  (fe_regions_wf_len_lit (-1)) ltac:(repeat constructor; cbn; lia)
  ltac:(constructor; [|constructor];
        apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8%N (SLit (-1)) SIZE_MAXZ);
        [ apply bv_eq; change (bv_unsigned (sv_denot (Ereg regs4 (fe_extra cx ++ [])) (SLit (-1))))
            with (U (Ereg regs4 (fe_extra cx ++ [])) (SLit (-1)));
          rewrite U_SLit; change (zcanon (-1)) with (2 ^ 64 - 1);
          rewrite (wz SIZE_MAXZ ltac:(unfold SIZE_MAXZ; lia)); reflexivity
        | cbn [Z.of_N]; unfold SIZE_MAXZ; lia | cbn [Z.of_N]; lia | exact Hlen4 ]))
  as (HJ2 & HARU2 & HS2).
apply (HN cx (Ereg regs4 (fe_extra cx ++ [])) (k + 0) ly4 S4 U3 W4
  (mkst regs4 (Z_to_bv 64 RA_alloc_live) mem4 (seg_rom tfibsegs)) md4 HB (fe_E_Ereg cx regs4 []) HJ2 HARU2);
  [|exact HS2].
exists text. split; [exact HU|].
split; [rewrite Habl; exact Hperm|].
split.
{ apply (s6_common B cx (k + 0) ly4 S4 U3 W4 (mkst regs4 (Z_to_bv 64 RA_alloc_live) mem4 (seg_rom tfibsegs)) md4 [(text, fe_n cx + 1)] (EV_check_no_overread + 1) HB HJ2 HARU2);
  [ rewrite Habl; exact Hperm
  | destruct Hcom as (Hk & _); lia
  | cbn [bsum fold_right snd]; lia ]. }
split.
{ split; [|split; [exact Hn3|]].
  - exact (s6_core_keep cx E ms W3 _ regs4 _ HS Hcore HP4
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)).
  - split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 19%bv 19 19 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E19|].
    split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 20%bv 20 20 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E20|].
    rewrite (s6_reg_keep E ms W3 _ regs4 _ 21%bv 21 21 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E21. }
split; [rewrite (ew_Ereg_nat regs4 (fe_extra cx ++ []) 10 10%bv eq_refl); exact E10|].
split.
{ apply (s6_cstr_carry B ly4 S4 U3 W4 mem4 md4 W3 (ms_mem ms) text (fe_n cx + 1) text (fe_tb cx)
    HARU2 ltac:(rewrite Habl; exact Htxt) ltac:(lia) ltac:(rewrite HU; intros r []) ltac:(lia) ltac:(lia));
    [|exact Hcstr'].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4 mem4 md4 0
    text (fe_n cx + 1) (a - text) HARU HJc OK4 PO4 Htxt ltac:(rewrite Habl; exact Htxt) ltac:(lia)
    ltac:(intros Hf; exact (inFP_nil _ Hf))). }
split; [exists peak; exact Hglob4|].
exact (s6_lensh_call cx ly3 S3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) [] ly4 S4 W4 mem4 md4 0
  ltac:(rewrite HU in HJc; exact HJc) Hin EF (fun Hf => inFP_nil _ Hf) Hlsh1).
Qed.

Lemma s6_step2 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_peak_reset [fe_len_lit (-1)]) INV6_2 ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_alloc_live [fe_len_lit (-1)]) INV6_1.
Proof.
intros POST HN cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
s6_open HB HINV.
destruct HINV as (text & HU & Hperm & Hcom & (Hcore & Hn3 & E19 & E20 & E21) & E10 & Hcstr & Hstat & Hlsh).
pose proof (s6_walk B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k HB HJ) as (Efrs & Hin & ELY & Etop & EF & EFL).
pose proof (s6_geom B cx ly3 S3 U3 W3 (ms_mem ms3) md3 HARU Hin EF EFL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof Hcore as (A8 & A9 & A2 & A18 & A24 & A25 & A3 & A4 & A26 & A27).
assert (HceilS : alloc_ceiling + LLVMF_STK <= fe_sp0 cx) by (unfold LLVMF_STK; lia).
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite A8; apply wz; lia).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite A24; apply wz; lia).
assert (U25 : bv_unsigned (ew E 25) = fe_SF cx)
  by (rewrite A25; apply wz; unfold kHighShadowEnd in *; lia).
assert (Htxt : In (text, fe_n cx + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1)
  by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
destruct Hstat as (peak & Hglob3).
pose proof HARU as HARU0.
pose proof (fe_ss_z_ok cx E _ _ (w_H W3) ms3 HS U25 Hlsh) as HSz. clear HS. rename HSz into HS.
fsw_aj_run_toU entry_tbl_ok HS HJ HARU A_fuzz_alloc_peak_reset.
{ apply (fe_awr_z B). exact (s6_awr B cx E ly3 S3 [fe_len_lit (-1)] U8 U24 U25 EF). }
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
pose proof (fe_lensh_of cx E _ (w_H W3) ms HS ltac:(vm_compute; reflexivity) U25) as Hlsh1.
pose proof (fe_drop_z E _ (w_H W3) ms HS ltac:(vm_compute; reflexivity)) as HSd. clear HS. rename HSd into HS.
pose proof (fe_frame_z E [fe_len_lit (-1)] _ _ HFr) as HFr'. clear HFr. rename HFr' into HFr.
assert (R1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_peak_reset)
  by (apply (fsw_reg_lit (w_H W3) E _ ms 1%bv RA_peak_reset HS);
      [vm_compute; reflexivity | unfold RA_peak_reset; lia]).
assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx)
  by (unfold spZ; rewrite (s6_reg_at E _ ms W3 2%bv 2 HS ltac:(vm_compute; reflexivity)), A2; apply wz; lia).
assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx)
  by (unfold s0Z; rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)), A8; apply wz; lia).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx))
  by (rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact A8).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact A24).
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact A18).
assert (R25 : YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx))
  by (rewrite (s6_reg_at E _ ms W3 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact A25).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = w64 (as_gp B))
  by (rewrite (s6_reg_at E _ ms W3 3%bv 3 HS ltac:(vm_compute; reflexivity)), A3; exact Hgp).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = w64 (as_tp B))
  by (rewrite (s6_reg_at E _ ms W3 4%bv 4 HS ltac:(vm_compute; reflexivity)), A4; exact Htp).
pose proof (s6_frame_at cx E W3 ms _ [fe_len_lit (-1)] HS ltac:(vm_compute; reflexivity) HE U8 U24
  ltac:(lia)) as (Hsv & Hflag & Hcsx).
destruct (s6_sv_words cx E W3 (ms_mem ms) HE Hsv) as (Hw1 & Hw2).
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 8) (raZ (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw1) as Hw1'.
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 16) (s0Z (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw2) as Hw2'.
destruct (s6_chain B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ Hw1' Hw2') as (ch & Hch).
assert (HK0 : 0 <= STK_fuzz_alloc) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HKb : STK_fuzz_alloc + 112 <= LLVMF_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hpre : fpreU tfibsegs B STK_fuzz_alloc ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch).
{ apply (s6_fpreU B cx ly3 S3 U3 W3 (ms_mem ms) mdc k (ms_regs ms) STK_fuzz_alloc ch HB HJ HARU
    (s6_arodata B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ HARU) Rsp HK0 HKb);
    [ rewrite R1; apply ret_ok_even; rewrite (wz RA_peak_reset ltac:(unfold RA_peak_reset; lia)); reflexivity
    | unfold raZ; rewrite R1, (wz RA_peak_reset ltac:(unfold RA_peak_reset; lia)); unfold RA_peak_reset; lia
    | exact R3 | exact R4 | rewrite Rsp, Rs0; exact Hch ]. }
assert (Hglob : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) peak (c_cnt cx + 3) SIZE_MAXZ).
{ apply (s6_glob_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hglob3].
  intros a Ha. exact (s6_run_img B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_lit (-1)] a
    HARU0 Hin EF U8 U24 U25 HceilS G6 HFr Ha). }
assert (Hcstr' : cstr_ok tfibsegs W3 (ms_mem ms) text (fe_tb cx)).
{ apply (s6_cstr_carry B ly3 S3 U3 W3 (ms_mem ms) mdc W3 (ms_mem ms3) text (fe_n cx + 1) text (fe_tb cx)
    HARU Htxt ltac:(lia) ltac:(rewrite HU; intros r []) ltac:(lia) ltac:(lia)); [|exact Hcstr].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_lit (-1)] text (fe_n cx + 1)
    (a - text) HARU0 Hin EF Htxt ltac:(lia) U8 U24 U25 HceilS G6 G7 HFr). }
assert (E10' : ew E 10 = Z_to_bv 64 (c_live cx)) by exact E10.
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (en_alloc_peak_reset ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch (c_live cx) peak (c_cnt cx + 3)
     SIZE_MAXZ Hpre ltac:(rewrite HU; apply s6_heads_nil) Hglob)|].
intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (Habl & Hglob4 & Hheads4)).
rewrite R1.
(* ---- back at 0x81118 ---- *)
assert (Hlen4 : val_mem tfibsegs (mrestrict (w_H W4) mem4) (fe_F cx + 32) 8 SIZE_MAXZ).
{ intros j Hj.
  rewrite (s6_keep_frame B cx ly3 S3 U3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) FS_PSTAT_FP ly4 S4
    U3 W4 mem4 md4 0 (fe_F cx + 32 + Z.of_nat j) HARU HJc OK4 PO4 Hin EF ltac:(lia)
    (s6_frame_not_pstat B cx ly3 S3 U3 W3 (ms_mem ms) mdc HARU Hin EF (fe_F cx + 32 + Z.of_nat j) ltac:(lia))).
  apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx) 32 8%N (SLit (-1)) SIZE_MAXZ
    (Forall_inv Hcsx)); [|cbn [Z.of_N]; unfold SIZE_MAXZ; lia|cbn [Z.of_N]; lia|exact Hj].
  apply bv_eq. change (bv_unsigned (sv_denot E (SLit (-1)))) with (U E (SLit (-1))).
  rewrite U_SLit. change (zcanon (-1)) with (2 ^ 64 - 1).
  rewrite (wz SIZE_MAXZ ltac:(unfold SIZE_MAXZ; lia)). reflexivity. }
destruct (s6_resume B cx ly3 S3 U3 W3 (ms_mem ms) mdc k STK_fuzz_alloc FS_PSTAT_FP (ms_regs ms) ly4 S4 U3 W4
  regs4 mem4 md4 0 E [] RA_peak_reset [fe_len_lit (-1)] HB HE HJ HARU HJc OK4 PO4
  (s6_pstat_sub B cx (c_ly cx) (c_S cx) ly3 S3)
  ltac:(intros a Ha; exact (s6_frame_not_pstat B cx ly3 S3 U3 W3 (ms_mem ms) mdc HARU Hin EF a ltac:(lia)))
  Rsp HK0 HKb Hsv Hflag HP4 R8 R24 R18 R25
  (fe_regions_wf_len_lit (-1)) ltac:(repeat constructor; cbn; lia)
  ltac:(constructor; [|constructor];
        apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8%N (SLit (-1)) SIZE_MAXZ);
        [ apply bv_eq; change (bv_unsigned (sv_denot (Ereg regs4 (fe_extra cx ++ [])) (SLit (-1))))
            with (U (Ereg regs4 (fe_extra cx ++ [])) (SLit (-1)));
          rewrite U_SLit; change (zcanon (-1)) with (2 ^ 64 - 1);
          rewrite (wz SIZE_MAXZ ltac:(unfold SIZE_MAXZ; lia)); reflexivity
        | cbn [Z.of_N]; unfold SIZE_MAXZ; lia | cbn [Z.of_N]; lia | exact Hlen4 ]))
  as (HJ2 & HARU2 & HS2).
apply (HN cx (Ereg regs4 (fe_extra cx ++ [])) (k + 0) ly4 S4 U3 W4
  (mkst regs4 (Z_to_bv 64 RA_peak_reset) mem4 (seg_rom tfibsegs)) md4 HB (fe_E_Ereg cx regs4 []) HJ2 HARU2);
  [|exact HS2].
exists text. split; [exact HU|].
split; [rewrite Habl; exact Hperm|].
split.
{ apply (s6_common B cx (k + 0) ly4 S4 U3 W4 (mkst regs4 (Z_to_bv 64 RA_peak_reset) mem4 (seg_rom tfibsegs))
    md4 [(text, fe_n cx + 1)] (EV_check_no_overread + 1) HB HJ2 HARU2);
  [ rewrite Habl; exact Hperm
  | destruct Hcom as (Hk & _); lia
  | cbn [bsum fold_right snd]; lia ]. }
split.
{ split; [|split; [exact Hn3|]].
  - exact (s6_core_keep cx E ms W3 _ regs4 _ HS Hcore HP4
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)).
  - split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 19%bv 19 19 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E19|].
    split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 20%bv 20 20 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E20|].
    rewrite (s6_reg_keep E ms W3 _ regs4 _ 21%bv 21 21 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E21. }
split.
{ rewrite (s6_reg_keep E ms W3 _ regs4 _ 23%bv 23 10 HS ltac:(vm_compute; reflexivity) HP4
    ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E10'. }
split.
{ apply (s6_cstr_carry B ly4 S4 U3 W4 mem4 md4 W3 (ms_mem ms) text (fe_n cx + 1) text (fe_tb cx)
    HARU2 ltac:(rewrite Habl; exact Htxt) ltac:(lia) ltac:(rewrite HU; intros r []) ltac:(lia) ltac:(lia));
    [|exact Hcstr'].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) FS_PSTAT_FP ly4 S4 U3 W4
    mem4 md4 0 text (fe_n cx + 1) (a - text) HARU HJc OK4 PO4 Htxt ltac:(rewrite Habl; exact Htxt) ltac:(lia)
    (s6_blk_not_pstat B ly3 S3 U3 W3 (ms_mem ms) mdc text (fe_n cx + 1) (a - text) HARU Htxt ltac:(lia))). }
split; [exact Hglob4|].
exact (s6_lensh_call cx ly3 S3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) FS_PSTAT_FP ly4 S4 W4 mem4 md4 0
  ltac:(rewrite HU in HJc; exact HJc) Hin EF (fe_lensh_npstat cx ltac:(lia)) Hlsh1).
Qed.

Lemma s6_step3 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_decode [fe_len_atom 46]) INV6_3 ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_peak_reset [fe_len_lit (-1)]) INV6_2.
Proof.
intros POST HN cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
s6_open HB HINV.
destruct HINV as (text & HU & Hperm & Hcom & (Hcore & Hn3 & E19 & E20 & E21) & E23 & Hcstr & Hglob3 & Hlsh).
pose proof (s6_walk B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k HB HJ) as (Efrs & Hin & ELY & Etop & EF & EFL).
pose proof (s6_geom B cx ly3 S3 U3 W3 (ms_mem ms3) md3 HARU Hin EF EFL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof Hcore as (A8 & A9 & A2 & A18 & A24 & A25 & A3 & A4 & A26 & A27).
assert (HceilS : alloc_ceiling + LLVMF_STK <= fe_sp0 cx) by (unfold LLVMF_STK; lia).
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite A8; apply wz; lia).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite A24; apply wz; lia).
assert (U25 : bv_unsigned (ew E 25) = fe_SF cx)
  by (rewrite A25; apply wz; unfold kHighShadowEnd in *; lia).
assert (Htxt : In (text, fe_n cx + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); left; reflexivity).
assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1)
  by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
assert (Hdecs : dec_size (fe_tb cx) = fe_n cx / 4 * 3 + 3)
  by (unfold dec_size; rewrite Htbl; reflexivity).
assert (Hdec3 : 3 <= dec_size (fe_tb cx) <= 3 * 2 ^ 20) by (rewrite Hdecs; Z.div_mod_to_equations; lia).
pose proof HARU as HARU0.
pose proof (fe_ss_z_ok cx E _ _ (w_H W3) ms3 HS U25 Hlsh) as HSz. clear HS. rename HSz into HS.
fsw_aj_run_toU entry_tbl_ok HS HJ HARU A_preset_base64_decode.
{ apply (fe_awr_z B). exact (s6_awr B cx E ly3 S3 [fe_len_lit (-1)] U8 U24 U25 EF). }
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
(* `len`'s shadow byte at the call: decode_spec_ff's range_addressable premise on *lenp (fe_lensh_ra) *)
pose proof (fe_lensh_of cx E _ (w_H W3) ms HS ltac:(vm_compute; reflexivity) U25) as Hlsh1.
pose proof (fe_drop_z E _ (w_H W3) ms HS ltac:(vm_compute; reflexivity)) as HSd. clear HS. rename HSd into HS.
pose proof (fe_frame_z E [fe_len_lit (-1)] _ _ HFr) as HFr'. clear HFr. rename HFr' into HFr.
assert (R1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_decode)
  by (apply (fsw_reg_lit (w_H W3) E _ ms 1%bv RA_decode HS);
      [vm_compute; reflexivity | unfold RA_decode; lia]).
assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx)
  by (unfold spZ; rewrite (s6_reg_at E _ ms W3 2%bv 2 HS ltac:(vm_compute; reflexivity)), A2; apply wz; lia).
assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx)
  by (unfold s0Z; rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)), A8; apply wz; lia).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx))
  by (rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact A8).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact A24).
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact A18).
assert (R25 : YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx))
  by (rewrite (s6_reg_at E _ ms W3 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact A25).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = w64 (as_gp B))
  by (rewrite (s6_reg_at E _ ms W3 3%bv 3 HS ltac:(vm_compute; reflexivity)), A3; exact Hgp).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = w64 (as_tp B))
  by (rewrite (s6_reg_at E _ ms W3 4%bv 4 HS ltac:(vm_compute; reflexivity)), A4; exact Htp).
assert (R10 : YK11.getr (ms_regs ms) 10%bv = w64 text)
  by (rewrite (s6_reg_at E _ ms W3 10%bv 21 HS ltac:(vm_compute; reflexivity)); exact E21).
assert (R11 : YK11.getr (ms_regs ms) 11%bv = w64 (fe_F cx + 32))
  by (rewrite (s6_reg_at E _ ms W3 11%bv 20 HS ltac:(vm_compute; reflexivity)); exact E20).
pose proof (s6_frame_at cx E W3 ms _ [fe_len_lit (-1)] HS ltac:(vm_compute; reflexivity) HE U8 U24
  ltac:(lia)) as (Hsv & Hflag & Hcsx).
destruct (s6_sv_words cx E W3 (ms_mem ms) HE Hsv) as (Hw1 & Hw2).
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 8) (raZ (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw1) as Hw1'.
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 16) (s0Z (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw2) as Hw2'.
destruct (s6_chain B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ Hw1' Hw2') as (ch & Hch).
assert (HK0 : 0 <= STK_preset_base64_decode) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HKb : STK_preset_base64_decode + 112 <= LLVMF_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hpre : fpreU tfibsegs B STK_preset_base64_decode ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch).
{ apply (s6_fpreU B cx ly3 S3 U3 W3 (ms_mem ms) mdc k (ms_regs ms) STK_preset_base64_decode ch HB HJ HARU
    (s6_arodata B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ HARU) Rsp HK0 HKb);
    [ rewrite R1; apply ret_ok_even; rewrite (wz RA_decode ltac:(unfold RA_decode; lia)); reflexivity
    | unfold raZ; rewrite R1, (wz RA_decode ltac:(unfold RA_decode; lia)); unfold RA_decode; lia
    | exact R3 | exact R4 | rewrite Rsp, Rs0; exact Hch ]. }
assert (Hglob : fs_glob tfibsegs W3 (ms_mem ms) (c_live cx) (c_live cx) (c_cnt cx + 3) SIZE_MAXZ).
{ apply (s6_glob_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hglob3].
  intros a Ha. exact (s6_run_img B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_lit (-1)] a
    HARU0 Hin EF U8 U24 U25 HceilS G6 HFr Ha). }
assert (Hcstr' : cstr_ok tfibsegs W3 (ms_mem ms) text (fe_tb cx)).
{ apply (s6_cstr_carry B ly3 S3 U3 W3 (ms_mem ms) mdc W3 (ms_mem ms3) text (fe_n cx + 1) text (fe_tb cx)
    HARU Htxt ltac:(lia) ltac:(rewrite HU; intros r []) ltac:(lia) ltac:(lia)); [|exact Hcstr].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_lit (-1)] text (fe_n cx + 1)
    (a - text) HARU0 Hin EF Htxt ltac:(lia) U8 U24 U25 HceilS G6 G7 HFr). }
(* the value the `len` slot holds at the call (fs.c:330 sets it to (size_t)-1 at 0x810a8) *)
assert (Hv : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx + 32) 8 SIZE_MAXZ).
{ apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx) 32 8%N (SLit (-1)) SIZE_MAXZ
    (Forall_inv Hcsx)); [|cbn [Z.of_N]; unfold SIZE_MAXZ; lia|cbn [Z.of_N]; lia].
  apply bv_eq. change (bv_unsigned (sv_denot E (SLit (-1)))) with (U E (SLit (-1))).
  rewrite U_SLit. change (zcanon (-1)) with (2 ^ 64 - 1).
  rewrite (wz SIZE_MAXZ ltac:(unfold SIZE_MAXZ; lia)). reflexivity. }
(* the text block and the entry's frame are disjoint (AR_sep_law) *)
pose proof (sep_block_frame tfibsegs B (AR_laws_ok tfibsegs B) ly3 S3 W3 (unpoison U3 (ms_mem ms)) mdc
  text (fe_n cx + 1) 0 (c_fpos cx) (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms) mdc HARU) Htxt Hin) as Hsep.
unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite EF, Hfb, Hrq in Hsep.
assert (Htext4096 : 4096 <= text).
{ destruct (al_blocks _ _ (AR_laws_ok tfibsegs B) ly3 S3 W3 (unpoison U3 (ms_mem ms)) mdc text (fe_n cx + 1)
    (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms) mdc HARU) Htxt) as (_ & H4 & _). exact H4. }
(* the room the decoder asks *)
pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
assert (Hroom1 : st_nev S3 + dec_ev (fe_tb cx) <= EV_MAX).
{ assert (Hdev : dec_ev (fe_tb cx) <= 2)
    by (unfold dec_ev; destruct (WriterSpec.b64_dec (fe_tb cx));
        unfold EV_fuzz_malloc, EV_preset_base64_decode; lia).
  destruct Hcom as (Hk & _); unfold EV_check_no_overread in Hk; unfold EV_LIB in *; lia. }
assert (Hroom2 : blocks_bytes S3 + (dec_size (fe_tb cx) + HEAD) <= LIVE_MAX).
{ rewrite (s6_bb B ly3 S3 (c_ly cx) (c_S cx) [(text, fe_n cx + 1)] Hperm).
  cbn [bsum fold_right snd]. unfold HEAD, YCfn.LIVE_LIB, LIVE_MAX in *. lia. }
rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind;
  [exact (en_decode ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch text (fe_F cx + 32) (fe_tb cx) (c_live cx)
     (c_live cx) (c_cnt cx + 3) SIZE_MAXZ SIZE_MAXZ Hpre ltac:(rewrite HU; apply s6_heads_nil)
     ltac:(rewrite Efrs; cbn [length]; unfold FRL_CRT_CALLEE; lia) R10 R11 Hcstr'
     ltac:(right; right; left; exists text, (fe_n cx + 1); split; [unfold HEAD; lia|]; split; [exact Htxt|];
           split; [lia|]; split; [rewrite length_app; cbn [length]; lia|]; rewrite HU; intros r [])
     Htbo ltac:(rewrite Htbl; lia)
     ltac:(Z.div_mod_to_equations; lia)
     ltac:(exists 0, (c_fpos cx); split; [exact Hin|]; intros a Ha; unfold frame_rng, in_zr; cbn [fst snd];
           rewrite EF, Hfb; lia)
     ltac:(intros a Ha;
           destruct (proj1 (proj2 (proj2 (al_frames _ _ (AR_laws_ok tfibsegs B) ly3 S3 W3
             (unpoison U3 (ms_mem ms)) mdc 0 (c_fpos cx)
             (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms) mdc HARU) Hin))) a
             ltac:(rewrite EF, Hfb; lia)) as (Hp & Hno);
           exact (fsw_apresent_notowned B ly3 S3 U3 W3 (ms_mem ms) mdc a HARU ltac:(lia) Hno Hp))
     (fe_lensh_ra cx (w_H W3) (ms_mem ms) ltac:(Z.div_mod_to_equations; lia) Hlsh1)
     Hv ltac:(unfold SIZE_MAXZ; lia)
     ltac:(rewrite Htbl; lia)
     Hglob Hroom1 Hroom2 ltac:(unfold YCfn.LIVE_LIB in Hlv; lia)
     ltac:(unfold FS_CNT_LIB in Hcnt; lia))|].
intros W4 c4 Hwle Hpost.
assert (Hmod : (c_cnt cx + 3 + 1) mod 2 ^ 64 = c_cnt cx + 4)
  by (rewrite Z.mod_small; unfold FS_CNT_LIB in Hcnt; lia).
assert (HnB : forall i, 0 <= i < req_size (fe_n cx + 1) ->
  ~ inFP (FS_PSTAT_FP ++ [(fe_F cx + 32, fe_F cx + 32 + 8)]) (text + i)).
{ intros i Hi Hf. destruct (s6_inFP_app _ _ _ Hf) as [Hp | Hl].
  - exact (s6_blk_not_pstat B ly3 S3 U3 W3 (ms_mem ms) mdc text (fe_n cx + 1) i HARU Htxt Hi Hp).
  - destruct Hl as (r & [<-|[]] & Ha). cbn [fst snd] in Ha. rewrite Hrq in Hi. lia. }
destruct Hpost as [(Hcf & _) | [(Hne & Hdnone & Hp2) | (q & out & Hne & Hdsome & Hq0 & Hp3)]].
- (* the one allocation refused: impossible, g_fail_at is SIZE_MAX and g_count stays under 2 ^ 63 *)
  exfalso. unfold SIZE_MAXZ, FS_CNT_LIB in *. lia.
- (* a bad text: body = 0, the `len` slot keeps SIZE_MAX *)
  destruct Hp2 as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (E10 & Hpe & Hvl & Hglob4)).
  (* the base's post is the equality of the two block lists (malloc then free of the same block) *)
  assert (Hpm : Permutation (ablocks B ly4 S4) (ablocks B ly3 S3)) by (rewrite Hpe; apply Permutation_refl).
  rewrite R1.
  destruct (s6_resume B cx ly3 S3 U3 W3 (ms_mem ms) mdc k STK_preset_base64_decode
    (FS_PSTAT_FP ++ [(fe_F cx + 32, fe_F cx + 32 + 8)]) (ms_regs ms) ly4 S4 U3 W4 regs4 mem4 md4
    EV_preset_base64_decode E [Z_to_bv 64 SIZE_MAXZ] RA_decode [fe_len_atom 46] HB HE HJ HARU HJc OK4 PO4
    (s6_dec_sub B cx (c_ly cx) (c_S cx) ly3 S3 (fe_F cx + 32) EF ltac:(lia) ltac:(lia))
    (s6_dec_flag B cx ly3 S3 U3 W3 (ms_mem ms) mdc (fe_F cx + 32) HARU Hin EF ltac:(lia))
    Rsp HK0 HKb Hsv Hflag HP4 R8 R24 R18 R25
    (fe_regions_wf_len_atom 46) ltac:(repeat constructor; cbn; lia)
    ltac:(constructor; [|constructor];
          apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8%N (SOff 46 0) SIZE_MAXZ);
          [ rewrite fsw_SOff0; change 46%nat with (32 + 14)%nat; rewrite ew_Ereg_extra;
            rewrite app_nth2; rewrite fe_extra_len; [|lia];
            replace (14 - 14)%nat with 0%nat by lia; reflexivity
          | cbn [Z.of_N]; unfold SIZE_MAXZ; lia | cbn [Z.of_N]; lia | exact Hvl ]))
    as (HJ2 & HARU2 & HS2).
  apply (HN cx (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 SIZE_MAXZ])) (k + EV_preset_base64_decode) ly4 S4 U3 W4
    (mkst regs4 (Z_to_bv 64 RA_decode) mem4 (seg_rom tfibsegs)) md4 HB
    (fe_E_Ereg cx regs4 [Z_to_bv 64 SIZE_MAXZ]) HJ2 HARU2); [|exact HS2].
  exists text, 0, SIZE_MAXZ.
  assert (Hperm4 : Permutation (ablocks B ly4 S4) ((text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)))
    by (apply (Permutation_trans Hpm); exact Hperm).
  assert (HE46 : ew (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 SIZE_MAXZ])) 46 = Z_to_bv 64 SIZE_MAXZ).
  { change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra, app_nth2; rewrite fe_extra_len; [|lia].
    replace (14 - 14)%nat with 0%nat by lia. reflexivity. }
  assert (Hcstr4 : cstr_ok tfibsegs W4 mem4 text (fe_tb cx)).
  { apply (s6_cstr_carry B ly4 S4 U3 W4 mem4 md4 W3 (ms_mem ms) text (fe_n cx + 1) text (fe_tb cx)
      HARU2 ltac:(apply (Permutation_in _ (Permutation_sym Hpm)); exact Htxt) ltac:(lia)
      ltac:(rewrite HU; intros r []) ltac:(lia) ltac:(lia)); [|exact Hcstr'].
    intros a Ha. replace a with (text + (a - text)) by lia.
    exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_preset_base64_decode (spZ (ms_regs ms))
      (FS_PSTAT_FP ++ [(fe_F cx + 32, fe_F cx + 32 + 8)]) ly4 S4 U3 W4 mem4 md4 EV_preset_base64_decode
      text (fe_n cx + 1) (a - text) HARU HJc OK4 PO4 Htxt
      ltac:(apply (Permutation_in _ (Permutation_sym Hpm)); exact Htxt) ltac:(lia)
      (HnB (a - text) ltac:(lia))). }
  split; [|split].
  + split; [rewrite HU; reflexivity|].
    split; [exact Hperm4|].
    split; [left; split; [exact Hdnone | split; reflexivity]|].
    split; [intros Hc; exfalso; exact (Hc eq_refl)|].
    split.
    { split; [|split; [exact Hn3|]].
      - exact (s6_core_keep cx E ms W3 _ regs4 _ HS Hcore HP4
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity)).
      - split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 19%bv 19 19 HS ltac:(vm_compute; reflexivity) HP4
            ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E19|].
        split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 20%bv 20 20 HS ltac:(vm_compute; reflexivity) HP4
            ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E20|].
        rewrite (s6_reg_keep E ms W3 _ regs4 _ 21%bv 21 21 HS ltac:(vm_compute; reflexivity) HP4
            ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E21. }
    split; [exact HE46|].
    split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 23%bv 23 23 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E23|].
    split; [exact Hcstr4|].
    assert (Hl6 : fe_live6 cx 0 = c_live cx) by (unfold fe_live6; cbn [Z.eqb]; lia).
    rewrite Hl6.
    replace (Z.max (c_live cx) (c_live cx + dec_size (fe_tb cx))) with (c_live cx + dec_size (fe_tb cx))
      in Hglob4 by lia.
    rewrite Hmod in Hglob4. exact Hglob4.
  + rewrite (ew_Ereg_nat regs4 (fe_extra cx ++ [Z_to_bv 64 SIZE_MAXZ]) 10 10%bv eq_refl). exact E10.
  + apply (s6_common B cx (k + EV_preset_base64_decode) ly4 S4 U3 W4
      (mkst regs4 (Z_to_bv 64 RA_decode) mem4 (seg_rom tfibsegs)) md4 [(text, fe_n cx + 1)]
      (EV_check_no_overread + 1 + EV_preset_base64_decode) HB HJ2 HARU2);
    [ exact Hperm4
    | destruct Hcom as (Hk & _); unfold EV_preset_base64_decode in *; lia
    | cbn [bsum fold_right snd]; lia ].
- (* success: body = q holds b64_dec tb and the `len` slot its length *)
  destruct Hp3 as (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 &
    (E10 & Hq4096 & Habl & Hrblk & Hzb & Hvl & Hcstr4 & Hglob4)).
  rewrite R1.
  pose proof (WriterSpecFacts.b64_dec_bound (fe_tb cx) out Hdsome) as Hob.
  rewrite Htbl in Hob.
  assert (Hqne : (q =? 0) = false) by (apply Z.eqb_neq; exact Hq0).
  destruct Hrblk as (Hrin & Hq16 & Hdpos & Hrhd).
  destruct (s6_resume B cx ly3 S3 U3 W3 (ms_mem ms) mdc k STK_preset_base64_decode
    (FS_PSTAT_FP ++ [(fe_F cx + 32, fe_F cx + 32 + 8)]) (ms_regs ms) ly4 S4 (U3 ++ [(q - HEAD, HEAD)]) W4
    regs4 mem4 md4 1 E [Z_to_bv 64 (Z.of_nat (length out))] RA_decode [fe_len_atom 46] HB HE HJ HARU HJc
    OK4 PO4
    (s6_dec_sub B cx (c_ly cx) (c_S cx) ly3 S3 (fe_F cx + 32) EF ltac:(lia) ltac:(lia))
    (s6_dec_flag B cx ly3 S3 U3 W3 (ms_mem ms) mdc (fe_F cx + 32) HARU Hin EF ltac:(lia))
    Rsp HK0 HKb Hsv Hflag HP4 R8 R24 R18 R25
    (fe_regions_wf_len_atom 46) ltac:(repeat constructor; cbn; lia)
    ltac:(constructor; [|constructor];
          apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8%N (SOff 46 0) (Z.of_nat (length out)));
          [ rewrite fsw_SOff0; change 46%nat with (32 + 14)%nat; rewrite ew_Ereg_extra;
            rewrite app_nth2; rewrite fe_extra_len; [|lia];
            replace (14 - 14)%nat with 0%nat by lia; reflexivity
          | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Hvl ]))
    as (HJ2 & HARU2 & HS2).
  apply (HN cx (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 (Z.of_nat (length out))])) (k + 1) ly4 S4
    (U3 ++ [(q - HEAD, HEAD)]) W4 (mkst regs4 (Z_to_bv 64 RA_decode) mem4 (seg_rom tfibsegs)) md4 HB
    (fe_E_Ereg cx regs4 [Z_to_bv 64 (Z.of_nat (length out))]) HJ2 HARU2); [|exact HS2].
  exists text, q, (Z.of_nat (length out)).
  assert (Hperm4 : Permutation (ablocks B ly4 S4)
    ([(q - HEAD, dec_size (fe_tb cx) + HEAD)] ++ (text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx))).
  { rewrite Habl. eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app].
    apply perm_skip. exact Hperm. }
  assert (HE46 : ew (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 (Z.of_nat (length out))])) 46
    = Z_to_bv 64 (Z.of_nat (length out))).
  { change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra, app_nth2; rewrite fe_extra_len; [|lia].
    replace (14 - 14)%nat with 0%nat by lia. reflexivity. }
  split; [|split].
  + split; [unfold fe_body_U; rewrite Hqne, HU; reflexivity|].
    split; [unfold fe_body_blocks; rewrite Hqne; exact Hperm4|].
    split.
    { right. exists out. split; [exact Hdsome|]. split; [exact Hq0|]. split; [reflexivity|].
      split; [exact Hq16|]. split; [unfold HEAD in *; lia|].
      split; [exact Hzb|]. split; [exact Hrhd|].
      split; [rewrite Habl; apply in_or_app; right; left; reflexivity|].
      apply in_or_app; right; left; reflexivity. }
    split.
    { intros _.
      pose proof (AR_laws_ok tfibsegs B) as LAWS.
      pose proof (ARU_AR tfibsegs B ly4 S4 (U3 ++ [(q - HEAD, HEAD)]) W4 mem4 md4 HARU2) as HAR4.
      assert (Hin4 : In (q - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly4 S4))
        by (rewrite Habl; apply in_or_app; right; left; reflexivity).
      assert (Hin4' : In (text, fe_n cx + 1) (ablocks B ly4 S4))
        by (rewrite Habl; apply in_or_app; left; exact Htxt).
      assert (Hrq2 : req_size (dec_size (fe_tb cx) + HEAD) = dec_size (fe_tb cx) + HEAD)
        by (unfold req_size; destruct (Z.eqb_spec (dec_size (fe_tb cx) + HEAD) 0); unfold HEAD in *; lia).
      destruct (list_eq_dec (fun x y : Z * Z => ltac:(decide equality; apply Z.eq_dec))
        [(q - HEAD, dec_size (fe_tb cx) + HEAD)] [(text, fe_n cx + 1)]) as [Hpair | Hpne].
      - exfalso. injection Hpair as Hp1 Hp2.
        destruct (al_sep _ _ LAWS ly4 S4 W4 (unpoison (U3 ++ [(q - HEAD, HEAD)]) mem4) md4 HAR4) as [Hp _].
        apply pairwise_app_l in Hp as [Hp _].
        apply in_split in Htxt as (l1 & l2 & El).
        assert (EL : map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) (ablocks B ly4 S4) =
          map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l1 ++ (text, req_size (fe_n cx + 1)) ::
          (map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) l2 ++ (text, req_size (fe_n cx + 1)) :: [])).
        { rewrite Habl, El, Hp1, Hp2, !map_app. cbn [map app fst snd]. rewrite <- app_assoc. reflexivity. }
        pose proof (YCbq.pairwise_In2 zdisjoint _ _ _ _ _ _ Hp EL) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq in Hd. lia.
      - pose proof (sep_blocks tfibsegs B LAWS ly4 S4 W4 (unpoison (U3 ++ [(q - HEAD, HEAD)]) mem4) md4
          (q - HEAD) (dec_size (fe_tb cx) + HEAD) text (fe_n cx + 1) HAR4 Hin4 Hin4'
          ltac:(intros Hc; apply Hpne; rewrite Hc; reflexivity)) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hrq, Hrq2 in Hd. unfold HEAD in *. lia. }
    split.
    { split; [|split; [exact Hn3|]].
      - exact (s6_core_keep cx E ms W3 _ regs4 _ HS Hcore HP4
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
          ltac:(vm_compute; reflexivity)).
      - split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 19%bv 19 19 HS ltac:(vm_compute; reflexivity) HP4
            ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E19|].
        split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 20%bv 20 20 HS ltac:(vm_compute; reflexivity) HP4
            ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E20|].
        rewrite (s6_reg_keep E ms W3 _ regs4 _ 21%bv 21 21 HS ltac:(vm_compute; reflexivity) HP4
            ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E21. }
    split; [exact HE46|].
    split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 23%bv 23 23 HS ltac:(vm_compute; reflexivity) HP4
        ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E23|].
    split; [exact Hcstr4|].
    unfold fe_live6. rewrite Hqne.
    replace (Z.max (c_live cx) (c_live cx + dec_size (fe_tb cx))) with (c_live cx + dec_size (fe_tb cx))
      in Hglob4 by lia.
    rewrite Hmod in Hglob4. exact Hglob4.
  + rewrite (ew_Ereg_nat regs4 (fe_extra cx ++ [Z_to_bv 64 (Z.of_nat (length out))]) 10 10%bv eq_refl).
    exact E10.
  + apply (s6_common B cx (k + 1) ly4 S4 (U3 ++ [(q - HEAD, HEAD)]) W4
      (mkst regs4 (Z_to_bv 64 RA_decode) mem4 (seg_rom tfibsegs)) md4
      ([(q - HEAD, dec_size (fe_tb cx) + HEAD)] ++ [(text, fe_n cx + 1)])
      (EV_check_no_overread + 1 + EV_preset_base64_decode) HB HJ2 HARU2);
    [ rewrite <- app_assoc; cbn [app]; exact Hperm4
    | destruct Hcom as (Hk & _); unfold EV_preset_base64_decode in *; lia
    | cbn [bsum fold_right snd app]; unfold HEAD; lia ].
Qed.

Lemma s6_step4 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_peak [fe_len_atom 46]) INV6_4 ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_decode [fe_len_atom 46]) INV6_3.
Proof.
intros POST HN cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
s6_open HB HINV.
destruct HINV as (text & body & l & (HU & Hperm & Hans & Hord & (Hcore & Hn3 & E19 & E20 & E21) & E46 & E23
  & Hcstr & Hglob3) & E10 & Hcom).
pose proof (s6_walk B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k HB HJ) as (Efrs & Hin & ELY & Etop & EF & EFL).
pose proof (s6_geom B cx ly3 S3 U3 W3 (ms_mem ms3) md3 HARU Hin EF EFL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof Hcore as (A8 & A9 & A2 & A18 & A24 & A25 & A3 & A4 & A26 & A27).
assert (HceilS : alloc_ceiling + LLVMF_STK <= fe_sp0 cx) by (unfold LLVMF_STK; lia).
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite A8; apply wz; lia).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite A24; apply wz; lia).
assert (U25 : bv_unsigned (ew E 25) = fe_SF cx)
  by (rewrite A25; apply wz; unfold kHighShadowEnd in *; lia).
assert (Hdecs : dec_size (fe_tb cx) = fe_n cx / 4 * 3 + 3)
  by (unfold dec_size; rewrite Htbl; reflexivity).
assert (Hdec3 : 3 <= dec_size (fe_tb cx) <= 3 * 2 ^ 20) by (rewrite Hdecs; Z.div_mod_to_equations; lia).
assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1)
  by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
assert (Hrqb : req_size (dec_size (fe_tb cx) + HEAD) = dec_size (fe_tb cx) + HEAD)
  by (unfold req_size; destruct (Z.eqb_spec (dec_size (fe_tb cx) + HEAD) 0); unfold HEAD in *; lia).
assert (Htxt : In (text, fe_n cx + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hl64 : 0 <= l < 2 ^ 64).
{ destruct Hans as [(_ & _ & ->) | (bs & Hd & _ & -> & _)]; [unfold SIZE_MAXZ; lia|].
  pose proof (WriterSpecFacts.b64_dec_bound _ _ Hd) as Hbb. rewrite Htbl in Hbb. lia. }
assert (Hbody : body <> 0 -> In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly3 S3)).
{ intros Hb0. destruct Hans as [(_ & Hb & _) | (bs & _ & _ & _ & _ & _ & _ & _ & Hinb & _)];
    [exfalso; exact (Hb0 Hb) | exact Hinb]. }
assert (Hheads : fs_heads B ly3 S3 U3).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [apply s6_heads_nil|].
  exact (s6_heads_one B ly3 S3 body (dec_size (fe_tb cx)) (Hbody Hb0) ltac:(lia)). }
assert (Hdist : forall r, In r U3 -> fst r + snd r <= text \/ text + Z.of_nat (length (fe_tb cx)) + 1 <= fst r).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [intros r []|].
  intros r [<-|[]]. cbn [fst snd]. rewrite Htbl. destruct (Hord Hb0); unfold HEAD in *; lia. }
assert (Hdisl : forall r, In r U3 -> fst r + snd r <= body \/ body + l <= fst r).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [intros r []|].
  intros r [<-|[]]. cbn [fst snd]. left. unfold HEAD. lia. }
assert (Hbsum : bsum (fe_body_blocks cx body ++ [(text, fe_n cx + 1)]) <= 2 ^ 32).
{ unfold fe_body_blocks. destruct (Z.eqb_spec body 0) as [->|Hb0];
    cbn [bsum fold_right snd app]; unfold HEAD in *; lia. }
pose proof HARU as HARU0.
fsw_aj_run_toU entry_tbl_ok HS HJ HARU A_fuzz_alloc_peak.
{ exact (s6_awr B cx E ly3 S3 [fe_len_atom 46] U8 U24 U25 EF). }
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (R1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_peak)
  by (apply (fsw_reg_lit (w_H W3) E _ ms 1%bv RA_peak HS);
      [vm_compute; reflexivity | unfold RA_peak; lia]).
assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx)
  by (unfold spZ; rewrite (s6_reg_at E _ ms W3 2%bv 2 HS ltac:(vm_compute; reflexivity)), A2; apply wz; lia).
assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx)
  by (unfold s0Z; rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)), A8; apply wz; lia).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx))
  by (rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact A8).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact A24).
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact A18).
assert (R25 : YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx))
  by (rewrite (s6_reg_at E _ ms W3 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact A25).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = w64 (as_gp B))
  by (rewrite (s6_reg_at E _ ms W3 3%bv 3 HS ltac:(vm_compute; reflexivity)), A3; exact Hgp).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = w64 (as_tp B))
  by (rewrite (s6_reg_at E _ ms W3 4%bv 4 HS ltac:(vm_compute; reflexivity)), A4; exact Htp).
pose proof (s6_frame_at cx E W3 ms _ [fe_len_atom 46] HS ltac:(vm_compute; reflexivity) HE U8 U24
  ltac:(lia)) as (Hsv & Hflag & Hcsx).
assert (Hvl0 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx + 32) 8 l).
{ apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx) 32 8%N (SOff 46 0) l
    (Forall_inv Hcsx)); [rewrite fsw_SOff0; exact E46 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
destruct (s6_sv_words cx E W3 (ms_mem ms) HE Hsv) as (Hw1 & Hw2).
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 8) (raZ (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw1) as Hw1'.
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 16) (s0Z (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw2) as Hw2'.
destruct (s6_chain B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ Hw1' Hw2') as (ch & Hch).
assert (HK0 : 0 <= STK_fuzz_alloc) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HKb : STK_fuzz_alloc + 112 <= LLVMF_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hpre : fpreU tfibsegs B STK_fuzz_alloc ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch).
{ apply (s6_fpreU B cx ly3 S3 U3 W3 (ms_mem ms) mdc k (ms_regs ms) STK_fuzz_alloc ch HB HJ HARU
    (s6_arodata B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ HARU) Rsp HK0 HKb);
    [ rewrite R1; apply ret_ok_even; rewrite (wz RA_peak ltac:(unfold RA_peak; lia)); reflexivity
    | unfold raZ; rewrite R1, (wz RA_peak ltac:(unfold RA_peak; lia)); unfold RA_peak; lia
    | exact R3 | exact R4 | rewrite Rsp, Rs0; exact Hch ]. }
assert (Hglob : fs_glob tfibsegs W3 (ms_mem ms) (fe_live6 cx body) (c_live cx + dec_size (fe_tb cx))
  (c_cnt cx + 4) SIZE_MAXZ).
{ apply (s6_glob_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hglob3].
  intros a Ha. exact (s6_run_img B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] a
    HARU0 Hin EF U8 U24 U25 HceilS G6 HFr Ha). }
assert (Hcstr' : cstr_ok tfibsegs W3 (ms_mem ms) text (fe_tb cx)).
{ apply (s6_cstr_carry B ly3 S3 U3 W3 (ms_mem ms) mdc W3 (ms_mem ms3) text (fe_n cx + 1) text (fe_tb cx)
    HARU Htxt ltac:(lia) Hdist ltac:(lia) ltac:(lia)); [|exact Hcstr].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] text (fe_n cx + 1)
    (a - text) HARU0 Hin EF Htxt ltac:(lia) U8 U24 U25 HceilS G6 G7 HFr). }
assert (Hans' : S6_ans cx ly3 S3 U3 W3 ms body l).
{ apply (s6_ans_keep cx ly3 S3 U3 W3 ms3 ly3 S3 W3 ms body l Hans); [intros Hb0; exact (Hbody Hb0)|].
  intros Hb0 a Ha. replace a with (body - HEAD + (a - (body - HEAD))) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] (body - HEAD)
    (dec_size (fe_tb cx) + HEAD) (a - (body - HEAD)) HARU0 Hin EF (Hbody Hb0) ltac:(unfold HEAD in *; lia)
    U8 U24 U25 HceilS G6 G7 HFr). }

rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind; [exact (en_alloc_peak ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch (fe_live6 cx body)
     (c_live cx + dec_size (fe_tb cx)) (c_cnt cx + 4) SIZE_MAXZ Hpre Hheads Hglob)|].
intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (E10' & Habl & Hglob4 & Hheads4)).
rewrite R1.
assert (Hvl : val_mem tfibsegs (mrestrict (w_H W4) mem4) (fe_F cx + 32) 8 l).
{ intros j Hj.
  rewrite (s6_keep_frame B cx ly3 S3 U3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4
    mem4 md4 0 (fe_F cx + 32 + Z.of_nat j) HARU HJc OK4 PO4 Hin EF ltac:(lia)
    ltac:(intros Hf; exact (inFP_nil _ Hf))).
  exact (Hvl0 j Hj). }
destruct (s6_resume B cx ly3 S3 U3 W3 (ms_mem ms) mdc k STK_fuzz_alloc [] (ms_regs ms) ly4 S4 U3 W4 regs4 mem4
  md4 0 E [Z_to_bv 64 l] RA_peak [fe_len_atom 46] HB HE HJ HARU HJc OK4 PO4
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) ltac:(intros a _ Hf; exact (inFP_nil a Hf))
  Rsp HK0 HKb Hsv Hflag HP4 R8 R24 R18 R25
  (fe_regions_wf_len_atom 46) ltac:(repeat constructor; cbn; lia)
  ltac:(constructor; [|constructor];
        apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8%N (SOff 46 0) l);
        [ rewrite fsw_SOff0; change 46%nat with (32 + 14)%nat; rewrite ew_Ereg_extra;
          rewrite app_nth2; rewrite fe_extra_len; [|lia];
          replace (14 - 14)%nat with 0%nat by lia; reflexivity
        | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Hvl ]))
  as (HJ2 & HARU2 & HS2).
apply (HN cx (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 l])) (k + 0) ly4 S4 U3 W4
  (mkst regs4 (Z_to_bv 64 RA_peak) mem4 (seg_rom tfibsegs)) md4 HB (fe_E_Ereg cx regs4 [Z_to_bv 64 l])
  HJ2 HARU2); [|exact HS2].
exists text, body, l.
assert (HE46' : ew (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 l])) 46 = Z_to_bv 64 l).
{ change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra, app_nth2; rewrite fe_extra_len; [|lia].
  replace (14 - 14)%nat with 0%nat by lia. reflexivity. }
assert (Htxt4 : In (text, fe_n cx + 1) (ablocks B ly4 S4)) by (rewrite Habl; exact Htxt).
split; [|split; [|split]].
+ split; [exact HU|].
  split; [rewrite Habl; exact Hperm|].
  split.
  { apply (s6_ans_keep cx ly3 S3 U3 W3 ms ly4 S4 W4
      (mkst regs4 (Z_to_bv 64 RA_peak) mem4 (seg_rom tfibsegs)) body l Hans');
    [ intros Hb0; rewrite Habl; exact (Hbody Hb0) |].
    intros Hb0 a Ha. cbn [ms_mem]. replace a with (body - HEAD + (a - (body - HEAD))) by lia.
    exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4 mem4 md4 0
      (body - HEAD) (dec_size (fe_tb cx) + HEAD) (a - (body - HEAD)) HARU HJc OK4 PO4 (Hbody Hb0)
      ltac:(rewrite Habl; exact (Hbody Hb0)) ltac:(unfold HEAD in *; lia)
      ltac:(intros Hf; exact (inFP_nil _ Hf))). }
  split; [exact Hord|].
  split.
  { split; [|split; [exact Hn3|]].
    - exact (s6_core_keep cx E ms W3 _ regs4 _ HS Hcore HP4
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity)).
    - split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 19%bv 19 19 HS ltac:(vm_compute; reflexivity) HP4
          ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E19|].
      split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 20%bv 20 20 HS ltac:(vm_compute; reflexivity) HP4
          ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E20|].
      rewrite (s6_reg_keep E ms W3 _ regs4 _ 21%bv 21 21 HS ltac:(vm_compute; reflexivity) HP4
          ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E21. }
  split; [exact HE46'|].
  split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 23%bv 23 23 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E23|].
  split.
  { apply (s6_cstr_carry B ly4 S4 U3 W4 mem4 md4 W3 (ms_mem ms) text (fe_n cx + 1) text (fe_tb cx)
      HARU2 Htxt4 ltac:(lia) Hdist ltac:(lia) ltac:(lia)); [|exact Hcstr'].
    intros a Ha. replace a with (text + (a - text)) by lia.
    exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_fuzz_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4 mem4 md4 0
      text (fe_n cx + 1) (a - text) HARU HJc OK4 PO4 Htxt Htxt4 ltac:(lia)
      ltac:(intros Hf; exact (inFP_nil _ Hf))). }
  exact Hglob4.
+ rewrite (s6_reg_keep E ms W3 _ regs4 _ 22%bv 22 10 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E10.
+ rewrite (ew_Ereg_nat regs4 (fe_extra cx ++ [Z_to_bv 64 l]) 10 10%bv eq_refl). exact E10'.
+ apply (s6_common B cx (k + 0) ly4 S4 U3 W4 (mkst regs4 (Z_to_bv 64 RA_peak) mem4 (seg_rom tfibsegs))
    md4 (fe_body_blocks cx body ++ [(text, fe_n cx + 1)])
    (EV_check_no_overread + 1 + EV_preset_base64_decode) HB HJ2 HARU2);
  [ rewrite Habl, <- app_assoc; cbn [app]; exact Hperm
  | destruct Hcom as (Hk & _); lia
  | exact Hbsum ].
Qed.

Lemma s6_step5 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_bounded [fe_len_atom 46]) INV6_5 ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_peak [fe_len_atom 46]) INV6_4.
Proof.
intros POST HN cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
s6_open HB HINV.
destruct HINV as (text & body & l & (HU & Hperm & Hans & Hord & (Hcore & Hn3 & E19 & E20 & E21) & E46 & E23
  & Hcstr & Hglob3) & E22 & E10 & Hcom).
pose proof (s6_walk B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k HB HJ) as (Efrs & Hin & ELY & Etop & EF & EFL).
pose proof (s6_geom B cx ly3 S3 U3 W3 (ms_mem ms3) md3 HARU Hin EF EFL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof Hcore as (A8 & A9 & A2 & A18 & A24 & A25 & A3 & A4 & A26 & A27).
assert (HceilS : alloc_ceiling + LLVMF_STK <= fe_sp0 cx) by (unfold LLVMF_STK; lia).
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite A8; apply wz; lia).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite A24; apply wz; lia).
assert (U25 : bv_unsigned (ew E 25) = fe_SF cx)
  by (rewrite A25; apply wz; unfold kHighShadowEnd in *; lia).
assert (Hdecs : dec_size (fe_tb cx) = fe_n cx / 4 * 3 + 3)
  by (unfold dec_size; rewrite Htbl; reflexivity).
assert (Hdec3 : 3 <= dec_size (fe_tb cx) <= 3 * 2 ^ 20) by (rewrite Hdecs; Z.div_mod_to_equations; lia).
assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1)
  by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
assert (Hrqb : req_size (dec_size (fe_tb cx) + HEAD) = dec_size (fe_tb cx) + HEAD)
  by (unfold req_size; destruct (Z.eqb_spec (dec_size (fe_tb cx) + HEAD) 0); unfold HEAD in *; lia).
assert (Htxt : In (text, fe_n cx + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hl64 : 0 <= l < 2 ^ 64).
{ destruct Hans as [(_ & _ & ->) | (bs & Hd & _ & -> & _)]; [unfold SIZE_MAXZ; lia|].
  pose proof (WriterSpecFacts.b64_dec_bound _ _ Hd) as Hbb. rewrite Htbl in Hbb. lia. }
assert (Hbody : body <> 0 -> In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly3 S3)).
{ intros Hb0. destruct Hans as [(_ & Hb & _) | (bs & _ & _ & _ & _ & _ & _ & _ & Hinb & _)];
    [exfalso; exact (Hb0 Hb) | exact Hinb]. }
assert (Hheads : fs_heads B ly3 S3 U3).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [apply s6_heads_nil|].
  exact (s6_heads_one B ly3 S3 body (dec_size (fe_tb cx)) (Hbody Hb0) ltac:(lia)). }
assert (Hdist : forall r, In r U3 -> fst r + snd r <= text \/ text + Z.of_nat (length (fe_tb cx)) + 1 <= fst r).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [intros r []|].
  intros r [<-|[]]. cbn [fst snd]. rewrite Htbl. destruct (Hord Hb0); unfold HEAD in *; lia. }
assert (Hdisl : forall r, In r U3 -> fst r + snd r <= body \/ body + l <= fst r).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [intros r []|].
  intros r [<-|[]]. cbn [fst snd]. left. unfold HEAD. lia. }
assert (Hbsum : bsum (fe_body_blocks cx body ++ [(text, fe_n cx + 1)]) <= 2 ^ 32).
{ unfold fe_body_blocks. destruct (Z.eqb_spec body 0) as [->|Hb0];
    cbn [bsum fold_right snd app]; unfold HEAD in *; lia. }
pose proof HARU as HARU0.
fsw_aj_run_toU entry_tbl_ok HS HJ HARU A_check_bounded_alloc.
{ exact (s6_awr B cx E ly3 S3 [fe_len_atom 46] U8 U24 U25 EF). }
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (R1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_bounded)
  by (apply (fsw_reg_lit (w_H W3) E _ ms 1%bv RA_bounded HS);
      [vm_compute; reflexivity | unfold RA_bounded; lia]).
assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx)
  by (unfold spZ; rewrite (s6_reg_at E _ ms W3 2%bv 2 HS ltac:(vm_compute; reflexivity)), A2; apply wz; lia).
assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx)
  by (unfold s0Z; rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)), A8; apply wz; lia).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx))
  by (rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact A8).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact A24).
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact A18).
assert (R25 : YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx))
  by (rewrite (s6_reg_at E _ ms W3 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact A25).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = w64 (as_gp B))
  by (rewrite (s6_reg_at E _ ms W3 3%bv 3 HS ltac:(vm_compute; reflexivity)), A3; exact Hgp).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = w64 (as_tp B))
  by (rewrite (s6_reg_at E _ ms W3 4%bv 4 HS ltac:(vm_compute; reflexivity)), A4; exact Htp).
pose proof (s6_frame_at cx E W3 ms _ [fe_len_atom 46] HS ltac:(vm_compute; reflexivity) HE U8 U24
  ltac:(lia)) as (Hsv & Hflag & Hcsx).
assert (Hvl0 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx + 32) 8 l).
{ apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx) 32 8%N (SOff 46 0) l
    (Forall_inv Hcsx)); [rewrite fsw_SOff0; exact E46 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
destruct (s6_sv_words cx E W3 (ms_mem ms) HE Hsv) as (Hw1 & Hw2).
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 8) (raZ (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw1) as Hw1'.
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 16) (s0Z (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw2) as Hw2'.
destruct (s6_chain B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ Hw1' Hw2') as (ch & Hch).
assert (HK0 : 0 <= STK_check_bounded_alloc) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HKb : STK_check_bounded_alloc + 112 <= LLVMF_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hpre : fpreU tfibsegs B STK_check_bounded_alloc ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch).
{ apply (s6_fpreU B cx ly3 S3 U3 W3 (ms_mem ms) mdc k (ms_regs ms) STK_check_bounded_alloc ch HB HJ HARU
    (s6_arodata B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ HARU) Rsp HK0 HKb);
    [ rewrite R1; apply ret_ok_even; rewrite (wz RA_bounded ltac:(unfold RA_bounded; lia)); reflexivity
    | unfold raZ; rewrite R1, (wz RA_bounded ltac:(unfold RA_bounded; lia)); unfold RA_bounded; lia
    | exact R3 | exact R4 | rewrite Rsp, Rs0; exact Hch ]. }
assert (Hglob : fs_glob tfibsegs W3 (ms_mem ms) (fe_live6 cx body) (c_live cx + dec_size (fe_tb cx))
  (c_cnt cx + 4) SIZE_MAXZ).
{ apply (s6_glob_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hglob3].
  intros a Ha. exact (s6_run_img B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] a
    HARU0 Hin EF U8 U24 U25 HceilS G6 HFr Ha). }
assert (Hcstr' : cstr_ok tfibsegs W3 (ms_mem ms) text (fe_tb cx)).
{ apply (s6_cstr_carry B ly3 S3 U3 W3 (ms_mem ms) mdc W3 (ms_mem ms3) text (fe_n cx + 1) text (fe_tb cx)
    HARU Htxt ltac:(lia) Hdist ltac:(lia) ltac:(lia)); [|exact Hcstr].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] text (fe_n cx + 1)
    (a - text) HARU0 Hin EF Htxt ltac:(lia) U8 U24 U25 HceilS G6 G7 HFr). }
assert (R10 : YK11.getr (ms_regs ms) 10%bv = w64 (dec_size (fe_tb cx))).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 10%bv HS).
  lazymatch type of HS with st_ok _ _ ?ss _ =>
    assert (Esr : sr_get (ss_regs ss) 10%bv = SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 23 0) (SLit (-1))))
      by (vm_compute; reflexivity) end.
  rewrite Esr, (s6_denot_sub E 10 23 (c_live cx + dec_size (fe_tb cx)) (c_live cx) E10 E23 ltac:(lia)
    ltac:(unfold YCfn.LIVE_LIB in Hlv; lia)).
  replace (c_live cx + dec_size (fe_tb cx) - c_live cx) with (dec_size (fe_tb cx)) by lia. reflexivity. }
assert (R11 : YK11.getr (ms_regs ms) 11%bv = w64 (fe_n cx))
  by (rewrite (s6_reg_at E _ ms W3 11%bv 19 HS ltac:(vm_compute; reflexivity)); exact E19).
assert (Hans' : S6_ans cx ly3 S3 U3 W3 ms body l).
{ apply (s6_ans_keep cx ly3 S3 U3 W3 ms3 ly3 S3 W3 ms body l Hans); [intros Hb0; exact (Hbody Hb0)|].
  intros Hb0 a Ha. replace a with (body - HEAD + (a - (body - HEAD))) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] (body - HEAD)
    (dec_size (fe_tb cx) + HEAD) (a - (body - HEAD)) HARU0 Hin EF (Hbody Hb0) ltac:(unfold HEAD in *; lia)
    U8 U24 U25 HceilS G6 G7 HFr). }

rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS eq_refl). cbn [ss_pc].
eapply SRr_bind; [exact (en_bounded_alloc ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch
     (dec_size (fe_tb cx)) (fe_n cx) (fe_live6 cx body) (c_live cx + dec_size (fe_tb cx)) (c_cnt cx + 4)
     SIZE_MAXZ Hpre Hheads Hglob R10 R11 ltac:(lia) ltac:(lia)
     ltac:(rewrite Hdecs; unfold b64_alloc_bound; lia))|].
intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (Habl & Hglob4)).
rewrite R1.
assert (Hvl : val_mem tfibsegs (mrestrict (w_H W4) mem4) (fe_F cx + 32) 8 l).
{ intros j Hj.
  rewrite (s6_keep_frame B cx ly3 S3 U3 W3 (ms_mem ms) mdc STK_check_bounded_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4
    mem4 md4 0 (fe_F cx + 32 + Z.of_nat j) HARU HJc OK4 PO4 Hin EF ltac:(lia)
    ltac:(intros Hf; exact (inFP_nil _ Hf))).
  exact (Hvl0 j Hj). }
destruct (s6_resume B cx ly3 S3 U3 W3 (ms_mem ms) mdc k STK_check_bounded_alloc [] (ms_regs ms) ly4 S4 U3 W4 regs4 mem4
  md4 0 E [Z_to_bv 64 l] RA_bounded [fe_len_atom 46] HB HE HJ HARU HJc OK4 PO4
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) ltac:(intros a _ Hf; exact (inFP_nil a Hf))
  Rsp HK0 HKb Hsv Hflag HP4 R8 R24 R18 R25
  (fe_regions_wf_len_atom 46) ltac:(repeat constructor; cbn; lia)
  ltac:(constructor; [|constructor];
        apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8%N (SOff 46 0) l);
        [ rewrite fsw_SOff0; change 46%nat with (32 + 14)%nat; rewrite ew_Ereg_extra;
          rewrite app_nth2; rewrite fe_extra_len; [|lia];
          replace (14 - 14)%nat with 0%nat by lia; reflexivity
        | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Hvl ]))
  as (HJ2 & HARU2 & HS2).
apply (HN cx (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 l])) (k + 0) ly4 S4 U3 W4
  (mkst regs4 (Z_to_bv 64 RA_bounded) mem4 (seg_rom tfibsegs)) md4 HB (fe_E_Ereg cx regs4 [Z_to_bv 64 l])
  HJ2 HARU2); [|exact HS2].
exists text, body, l.
assert (HE46' : ew (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 l])) 46 = Z_to_bv 64 l).
{ change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra, app_nth2; rewrite fe_extra_len; [|lia].
  replace (14 - 14)%nat with 0%nat by lia. reflexivity. }
assert (Htxt4 : In (text, fe_n cx + 1) (ablocks B ly4 S4)) by (rewrite Habl; exact Htxt).
split; [|split].
+ split; [exact HU|].
  split; [rewrite Habl; exact Hperm|].
  split.
  { apply (s6_ans_keep cx ly3 S3 U3 W3 ms ly4 S4 W4
      (mkst regs4 (Z_to_bv 64 RA_bounded) mem4 (seg_rom tfibsegs)) body l Hans');
    [ intros Hb0; rewrite Habl; exact (Hbody Hb0) |].
    intros Hb0 a Ha. cbn [ms_mem]. replace a with (body - HEAD + (a - (body - HEAD))) by lia.
    exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_check_bounded_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4 mem4 md4 0
      (body - HEAD) (dec_size (fe_tb cx) + HEAD) (a - (body - HEAD)) HARU HJc OK4 PO4 (Hbody Hb0)
      ltac:(rewrite Habl; exact (Hbody Hb0)) ltac:(unfold HEAD in *; lia)
      ltac:(intros Hf; exact (inFP_nil _ Hf))). }
  split; [exact Hord|].
  split.
  { split; [|split; [exact Hn3|]].
    - exact (s6_core_keep cx E ms W3 _ regs4 _ HS Hcore HP4
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
        ltac:(vm_compute; reflexivity)).
    - split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 19%bv 19 19 HS ltac:(vm_compute; reflexivity) HP4
          ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E19|].
      split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 20%bv 20 20 HS ltac:(vm_compute; reflexivity) HP4
          ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E20|].
      rewrite (s6_reg_keep E ms W3 _ regs4 _ 21%bv 21 21 HS ltac:(vm_compute; reflexivity) HP4
          ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E21. }
  split; [exact HE46'|].
  split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 23%bv 23 23 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E23|].
  split.
  { apply (s6_cstr_carry B ly4 S4 U3 W4 mem4 md4 W3 (ms_mem ms) text (fe_n cx + 1) text (fe_tb cx)
      HARU2 Htxt4 ltac:(lia) Hdist ltac:(lia) ltac:(lia)); [|exact Hcstr'].
    intros a Ha. replace a with (text + (a - text)) by lia.
    exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_check_bounded_alloc (spZ (ms_regs ms)) [] ly4 S4 U3 W4 mem4 md4 0
      text (fe_n cx + 1) (a - text) HARU HJc OK4 PO4 Htxt Htxt4 ltac:(lia)
      ltac:(intros Hf; exact (inFP_nil _ Hf))). }
  exact Hglob4.
+ rewrite (s6_reg_keep E ms W3 _ regs4 _ 22%bv 22 22 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E22.
+ apply (s6_common B cx (k + 0) ly4 S4 U3 W4 (mkst regs4 (Z_to_bv 64 RA_bounded) mem4 (seg_rom tfibsegs))
    md4 (fe_body_blocks cx body ++ [(text, fe_n cx + 1)])
    (EV_check_no_overread + 1 + EV_preset_base64_decode) HB HJ2 HARU2);
  [ rewrite Habl, <- app_assoc; cbn [app]; exact Hperm
  | destruct Hcom as (Hk & _); lia
  | exact Hbsum ].
Qed.

Lemma s6_step6 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_caw [fe_len_atom 46]) (INV_C6 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_bounded [fe_len_atom 46]) INV6_5.
Proof.
intros POST HN cx E k ly3 S3 U3 W3 ms3 md3 HB HE HJ HARU HINV HS.
s6_open HB HINV.
destruct HINV as (text & body & l & (HU & Hperm & Hans & Hord & (Hcore & Hn3 & E19 & E20 & E21) & E46 & E23
  & Hcstr & Hglob3) & E22 & Hcom).
pose proof (s6_walk B cx ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k HB HJ) as (Efrs & Hin & ELY & Etop & EF & EFL).
pose proof (s6_geom B cx ly3 S3 U3 W3 (ms_mem ms3) md3 HARU Hin EF EFL) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
pose proof Hcore as (A8 & A9 & A2 & A18 & A24 & A25 & A3 & A4 & A26 & A27).
assert (HceilS : alloc_ceiling + LLVMF_STK <= fe_sp0 cx) by (unfold LLVMF_STK; lia).
assert (U8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite A8; apply wz; lia).
assert (U24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite A24; apply wz; lia).
assert (U25 : bv_unsigned (ew E 25) = fe_SF cx)
  by (rewrite A25; apply wz; unfold kHighShadowEnd in *; lia).
assert (Hdecs : dec_size (fe_tb cx) = fe_n cx / 4 * 3 + 3)
  by (unfold dec_size; rewrite Htbl; reflexivity).
assert (Hdec3 : 3 <= dec_size (fe_tb cx) <= 3 * 2 ^ 20) by (rewrite Hdecs; Z.div_mod_to_equations; lia).
assert (Hrq : req_size (fe_n cx + 1) = fe_n cx + 1)
  by (unfold req_size; destruct (Z.eqb_spec (fe_n cx + 1) 0); lia).
assert (Hrqb : req_size (dec_size (fe_tb cx) + HEAD) = dec_size (fe_tb cx) + HEAD)
  by (unfold req_size; destruct (Z.eqb_spec (dec_size (fe_tb cx) + HEAD) 0); unfold HEAD in *; lia).
assert (Htxt : In (text, fe_n cx + 1) (ablocks B ly3 S3))
  by (apply (Permutation_in _ (Permutation_sym Hperm)); apply in_or_app; right; left; reflexivity).
assert (Hl64 : 0 <= l < 2 ^ 64).
{ destruct Hans as [(_ & _ & ->) | (bs & Hd & _ & -> & _)]; [unfold SIZE_MAXZ; lia|].
  pose proof (WriterSpecFacts.b64_dec_bound _ _ Hd) as Hbb. rewrite Htbl in Hbb. lia. }
assert (Hbody : body <> 0 -> In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly3 S3)).
{ intros Hb0. destruct Hans as [(_ & Hb & _) | (bs & _ & _ & _ & _ & _ & _ & _ & Hinb & _)];
    [exfalso; exact (Hb0 Hb) | exact Hinb]. }
assert (Hheads : fs_heads B ly3 S3 U3).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [apply s6_heads_nil|].
  exact (s6_heads_one B ly3 S3 body (dec_size (fe_tb cx)) (Hbody Hb0) ltac:(lia)). }
assert (Hdist : forall r, In r U3 -> fst r + snd r <= text \/ text + Z.of_nat (length (fe_tb cx)) + 1 <= fst r).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [intros r []|].
  intros r [<-|[]]. cbn [fst snd]. rewrite Htbl. destruct (Hord Hb0); unfold HEAD in *; lia. }
assert (Hdisl : forall r, In r U3 -> fst r + snd r <= body \/ body + l <= fst r).
{ rewrite HU. unfold fe_body_U. destruct (Z.eqb_spec body 0) as [->|Hb0]; [intros r []|].
  intros r [<-|[]]. cbn [fst snd]. left. unfold HEAD. lia. }
assert (Hbsum : bsum (fe_body_blocks cx body ++ [(text, fe_n cx + 1)]) <= 2 ^ 32).
{ unfold fe_body_blocks. destruct (Z.eqb_spec body 0) as [->|Hb0];
    cbn [bsum fold_right snd app]; unfold HEAD in *; lia. }
pose proof HARU as HARU0.
(* `ld a2, 0(s4)` at 0x81138 reads `len` through s4: re-express s4 as the frame atom + 32 (YI08.st_ok_set_reg) *)
assert (HS20 : st_ok tfibsegs E
  (mkSS (ss_pc (fe_ss RA_bounded [fe_len_atom 46])) (sr_set (ss_regs (fe_ss RA_bounded [fe_len_atom 46])) 20%bv
     (SOff 24 32)) (ss_mem (fe_ss RA_bounded [fe_len_atom 46])) (ss_resv (fe_ss RA_bounded [fe_len_atom 46]))
     (ss_facts (fe_ss RA_bounded [fe_len_atom 46]))) (restrict (w_H W3) ms3)).
{ apply (st_ok_set_reg tfibsegs E (fe_ss RA_bounded [fe_len_atom 46]) (restrict (w_H W3) ms3) 20%bv
    (SOff 24 32) HS ltac:(intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate Hc)).
  cbn [restrict ms_regs]. apply bv_eq.
  rewrite (s6_reg_at E (fe_ss RA_bounded [fe_len_atom 46]) ms3 W3 20%bv 20 HS ltac:(vm_compute; reflexivity)).
  rewrite E20, denot_SOff, A24, (wz (fe_F cx) ltac:(lia)), (wz (fe_F cx + 32) ltac:(lia)).
  symmetry. apply zcanon_id. unfold M64. lia. }
clear HS. rename HS20 into HS.
fsw_aj_run_toU entry_tbl_ok HS HJ HARU A_check_as_written.
{ cbn [ss_mem]. exact (s6_awr B cx E ly3 S3 [fe_len_atom 46] U8 U24 U25 EF). }
set (mdc := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (R1 : YK11.getr (ms_regs ms) 1%bv = Z_to_bv 64 RA_caw)
  by (apply (fsw_reg_lit (w_H W3) E _ ms 1%bv RA_caw HS);
      [vm_compute; reflexivity | unfold RA_caw; lia]).
assert (Rsp : spZ (ms_regs ms) = fe_sp1 cx)
  by (unfold spZ; rewrite (s6_reg_at E _ ms W3 2%bv 2 HS ltac:(vm_compute; reflexivity)), A2; apply wz; lia).
assert (Rs0 : s0Z (ms_regs ms) = fe_sp0 cx)
  by (unfold s0Z; rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)), A8; apply wz; lia).
assert (R8 : YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx))
  by (rewrite (s6_reg_at E _ ms W3 8%bv 8 HS ltac:(vm_compute; reflexivity)); exact A8).
assert (R24 : YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 24%bv 24 HS ltac:(vm_compute; reflexivity)); exact A24).
assert (R18 : YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx))
  by (rewrite (s6_reg_at E _ ms W3 18%bv 18 HS ltac:(vm_compute; reflexivity)); exact A18).
assert (R25 : YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx))
  by (rewrite (s6_reg_at E _ ms W3 25%bv 25 HS ltac:(vm_compute; reflexivity)); exact A25).
assert (R3 : YK11.getr (ms_regs ms) 3%bv = w64 (as_gp B))
  by (rewrite (s6_reg_at E _ ms W3 3%bv 3 HS ltac:(vm_compute; reflexivity)), A3; exact Hgp).
assert (R4 : YK11.getr (ms_regs ms) 4%bv = w64 (as_tp B))
  by (rewrite (s6_reg_at E _ ms W3 4%bv 4 HS ltac:(vm_compute; reflexivity)), A4; exact Htp).
pose proof (s6_frame_at cx E W3 ms _ [fe_len_atom 46] HS ltac:(vm_compute; reflexivity) HE U8 U24
  ltac:(lia)) as (Hsv & Hflag & Hcsx).
assert (Hvl0 : val_mem tfibsegs (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx + 32) 8 l).
{ apply (val_of_chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms)) (fe_F cx) 32 8%N (SOff 46 0) l
    (Forall_inv Hcsx)); [rewrite fsw_SOff0; exact E46 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
destruct (s6_sv_words cx E W3 (ms_mem ms) HE Hsv) as (Hw1 & Hw2).
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 8) (raZ (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw1) as Hw1'.
pose proof (s6_rdword_unpoison B ly3 S3 U3 W3 (ms_mem ms) mdc (fe_sp0 cx - 16) (s0Z (c_regs cx)) HARU
  ltac:(lia) ltac:(lia) Hw2) as Hw2'.
destruct (s6_chain B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ Hw1' Hw2') as (ch & Hch).
assert (HK0 : 0 <= STK_check_as_written) by (apply Z.leb_le; vm_compute; reflexivity).
assert (HKb : STK_check_as_written + 112 <= LLVMF_STK) by (apply Z.leb_le; vm_compute; reflexivity).
assert (Hpre : fpreU tfibsegs B STK_check_as_written ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch).
{ apply (s6_fpreU B cx ly3 S3 U3 W3 (ms_mem ms) mdc k (ms_regs ms) STK_check_as_written ch HB HJ HARU
    (s6_arodata B cx ly3 S3 U3 W3 (ms_mem ms) mdc k HB HJ HARU) Rsp HK0 HKb);
    [ rewrite R1; apply ret_ok_even; rewrite (wz RA_caw ltac:(unfold RA_caw; lia)); reflexivity
    | unfold raZ; rewrite R1, (wz RA_caw ltac:(unfold RA_caw; lia)); unfold RA_caw; lia
    | exact R3 | exact R4 | rewrite Rsp, Rs0; exact Hch ]. }
assert (Hglob : fs_glob tfibsegs W3 (ms_mem ms) (fe_live6 cx body) (c_live cx + dec_size (fe_tb cx))
  (c_cnt cx + 4) SIZE_MAXZ).
{ apply (s6_glob_keep W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hglob3].
  intros a Ha. exact (s6_run_img B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] a
    HARU0 Hin EF U8 U24 U25 HceilS G6 HFr Ha). }
assert (Hcstr' : cstr_ok tfibsegs W3 (ms_mem ms) text (fe_tb cx)).
{ apply (s6_cstr_carry B ly3 S3 U3 W3 (ms_mem ms) mdc W3 (ms_mem ms3) text (fe_n cx + 1) text (fe_tb cx)
    HARU Htxt ltac:(lia) Hdist ltac:(lia) ltac:(lia)); [|exact Hcstr].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] text (fe_n cx + 1)
    (a - text) HARU0 Hin EF Htxt ltac:(lia) U8 U24 U25 HceilS G6 G7 HFr). }
assert (R10 : YK11.getr (ms_regs ms) 10%bv = w64 text)
  by (rewrite (s6_reg_at E _ ms W3 10%bv 21 HS ltac:(vm_compute; reflexivity)); exact E21).
assert (R11 : YK11.getr (ms_regs ms) 11%bv = w64 body)
  by (rewrite (s6_reg_at E _ ms W3 11%bv 22 HS ltac:(vm_compute; reflexivity)); exact E22).
assert (R12 : YK11.getr (ms_regs ms) 12%bv = w64 l)
  by (rewrite (s6_reg_at E _ ms W3 12%bv 46 HS ltac:(vm_compute; reflexivity)); exact E46).
assert (Hans' : S6_ans cx ly3 S3 U3 W3 ms body l).
{ apply (s6_ans_keep cx ly3 S3 U3 W3 ms3 ly3 S3 W3 ms body l Hans); [intros Hb0; exact (Hbody Hb0)|].
  intros Hb0 a Ha. replace a with (body - HEAD + (a - (body - HEAD))) by lia.
  exact (s6_run_blk B cx E ly3 S3 U3 W3 (ms_mem ms3) (ms_mem ms) md3 [fe_len_atom 46] (body - HEAD)
    (dec_size (fe_tb cx) + HEAD) (a - (body - HEAD)) HARU0 Hin EF (Hbody Hb0) ltac:(unfold HEAD in *; lia)
    U8 U24 U25 HceilS G6 G7 HFr). }

rewrite (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS eq_refl). cbn [ss_pc].
assert (Hroom1 : st_nev S3 + EV_check_as_written <= EV_MAX).
{ pose proof HJ as (_ & _ & _ & _ & _ & _ & Hnev & _).
  destruct Hcom as (Hk & _). unfold EV_check_no_overread, EV_preset_base64_decode in Hk.
  unfold EV_check_as_written, EV_LIB in *. lia. }
assert (Hroom2 : blocks_bytes S3 + FSH_Fn_checks.LIVE_check_as_written <= LIVE_MAX).
{ rewrite (s6_bb B ly3 S3 (c_ly cx) (c_S cx) (fe_body_blocks cx body ++ [(text, fe_n cx + 1)])
    ltac:(rewrite <- app_assoc; cbn [app]; exact Hperm)).
  unfold FSH_Fn_checks.LIVE_check_as_written, YCfn.LIVE_LIB, LIVE_MAX in *. lia. }
eapply SRr_bind; [exact (en_as_written ly3 S3 U3 W3 (ms_regs ms) (ms_mem ms) mdc ch text body l (fe_tb cx)
     (fe_live6 cx body) (c_live cx + dec_size (fe_tb cx)) (c_cnt cx + 4) SIZE_MAXZ Hpre Hheads
     R10 R11 R12 Hcstr'
     ltac:(left; exists text, (fe_n cx + 1); split; [exact Htxt|]; split; [lia|];
           split; [rewrite Htbl; lia|]; intros r Hr; destruct (Hdist r Hr); [right|left]; assumption)
     ltac:(rewrite Htbl; unfold PRESET_FILE_MAX_BYTES; lia)
     (s6_answer cx ly3 S3 U3 W3 ms mdc body l HARU Hdisl Hans')
     Hglob Hroom1 Hroom2)|].
intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJc & OK4 & PO4 & HP4 & (Hpm & Hglob4)).
rewrite R1.
assert (Hvl : val_mem tfibsegs (mrestrict (w_H W4) mem4) (fe_F cx + 32) 8 l).
{ intros j Hj.
  rewrite (s6_keep_frame B cx ly3 S3 U3 W3 (ms_mem ms) mdc STK_check_as_written (spZ (ms_regs ms)) [] ly4 S4 U3 W4
    mem4 md4 EV_check_as_written (fe_F cx + 32 + Z.of_nat j) HARU HJc OK4 PO4 Hin EF ltac:(lia)
    ltac:(intros Hf; exact (inFP_nil _ Hf))).
  exact (Hvl0 j Hj). }
destruct (s6_resume B cx ly3 S3 U3 W3 (ms_mem ms) mdc k STK_check_as_written [] (ms_regs ms) ly4 S4 U3 W4 regs4 mem4
  md4 EV_check_as_written E [Z_to_bv 64 l] RA_caw [fe_len_atom 46] HB HE HJ HARU HJc OK4 PO4
  ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) ltac:(intros a _ Hf; exact (inFP_nil a Hf))
  Rsp HK0 HKb Hsv Hflag HP4 R8 R24 R18 R25
  (fe_regions_wf_len_atom 46) ltac:(repeat constructor; cbn; lia)
  ltac:(constructor; [|constructor];
        apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8%N (SOff 46 0) l);
        [ rewrite fsw_SOff0; change 46%nat with (32 + 14)%nat; rewrite ew_Ereg_extra;
          rewrite app_nth2; rewrite fe_extra_len; [|lia];
          replace (14 - 14)%nat with 0%nat by lia; reflexivity
        | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Hvl ]))
  as (HJ2 & HARU2 & HS2).
apply (HN cx (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 l])) (k + EV_check_as_written) ly4 S4 U3 W4
  (mkst regs4 (Z_to_bv 64 RA_caw) mem4 (seg_rom tfibsegs)) md4 HB (fe_E_Ereg cx regs4 [Z_to_bv 64 l])
  HJ2 HARU2); [|exact HS2].
exists text, body, l.
assert (HE46' : ew (Ereg regs4 (fe_extra cx ++ [Z_to_bv 64 l])) 46 = Z_to_bv 64 l).
{ change 46%nat with (32 + 14)%nat. rewrite ew_Ereg_extra, app_nth2; rewrite fe_extra_len; [|lia].
  replace (14 - 14)%nat with 0%nat by lia. reflexivity. }
assert (Htxt4 : In (text, fe_n cx + 1) (ablocks B ly4 S4))
  by (apply (Permutation_in _ (Permutation_sym Hpm)); exact Htxt).
assert (Hbody4 : body <> 0 -> In (body - HEAD, dec_size (fe_tb cx) + HEAD) (ablocks B ly4 S4))
  by (intros Hb0; apply (Permutation_in _ (Permutation_sym Hpm)); exact (Hbody Hb0)).
assert (Hans4 : S6_ans cx ly4 S4 U3 W4 (mkst regs4 (Z_to_bv 64 RA_caw) mem4 (seg_rom tfibsegs)) body l).
{ apply (s6_ans_keep cx ly3 S3 U3 W3 ms ly4 S4 W4
    (mkst regs4 (Z_to_bv 64 RA_caw) mem4 (seg_rom tfibsegs)) body l Hans' Hbody4).
  intros Hb0 a Ha. cbn [ms_mem]. replace a with (body - HEAD + (a - (body - HEAD))) by lia.
  exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_check_as_written (spZ (ms_regs ms)) [] ly4 S4 U3 W4
    mem4 md4 EV_check_as_written (body - HEAD) (dec_size (fe_tb cx) + HEAD) (a - (body - HEAD)) HARU HJc
    OK4 PO4 (Hbody Hb0) (Hbody4 Hb0) ltac:(unfold HEAD in *; lia) ltac:(intros Hf; exact (inFP_nil _ Hf))). }
assert (Hcstr4 : cstr_ok tfibsegs W4 mem4 text (fe_tb cx)).
{ apply (s6_cstr_carry B ly4 S4 U3 W4 mem4 md4 W3 (ms_mem ms) text (fe_n cx + 1) text (fe_tb cx)
    HARU2 Htxt4 ltac:(lia) Hdist ltac:(lia) ltac:(lia)); [|exact Hcstr'].
  intros a Ha. replace a with (text + (a - text)) by lia.
  exact (s6_keep_blk B ly3 S3 U3 W3 (ms_mem ms) mdc STK_check_as_written (spZ (ms_regs ms)) [] ly4 S4 U3 W4
    mem4 md4 EV_check_as_written text (fe_n cx + 1) (a - text) HARU HJc OK4 PO4 Htxt Htxt4 ltac:(lia)
    ltac:(intros Hf; exact (inFP_nil _ Hf))). }
split; [|split].
+ split; [exact HU|].
  split; [apply (Permutation_trans Hpm); exact Hperm|].
  split.
  { apply (s6_answer cx ly4 S4 U3 W4 (mkst regs4 (Z_to_bv 64 RA_caw) mem4 (seg_rom tfibsegs)) md4 body l
      HARU2 Hdisl Hans4). }
  split.
  { exact (s6_core_keep cx E ms W3 _ regs4 _ HS Hcore HP4
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
      ltac:(vm_compute; reflexivity)). }
  split; [exact Hn3|].
  split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 19%bv 19 19 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E19|].
  split.
  { rewrite (ew_Ereg_nat regs4 (fe_extra cx ++ [Z_to_bv 64 l]) 20 20%bv eq_refl),
      (fsw_pres (ms_regs ms) regs4 20%bv HP4
        ltac:(unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
              let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia)),
      (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 20%bv HS).
    lazymatch type of HS with st_ok _ _ ?ss _ =>
      assert (Esr20 : sr_get (ss_regs ss) 20%bv = SOff 24 32) by (vm_compute; reflexivity) end.
    rewrite Esr20. apply bv_eq.
    rewrite denot_SOff, A24, (wz (fe_F cx) ltac:(lia)), (wz (fe_F cx + 32) ltac:(lia)).
    apply zcanon_id. unfold M64. lia. }
  split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 21%bv 21 21 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E21|].
  split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 22%bv 22 22 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E22|].
  split; [rewrite (s6_reg_keep E ms W3 _ regs4 _ 23%bv 23 23 HS ltac:(vm_compute; reflexivity) HP4
      ltac:(unfold acallee_saved; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) eq_refl); exact E23|].
  split; [exact HE46' | exact Hcstr4].
+ apply (s6_common B cx (k + EV_check_as_written) ly4 S4 U3 W4
    (mkst regs4 (Z_to_bv 64 RA_caw) mem4 (seg_rom tfibsegs)) md4
    (fe_body_blocks cx body ++ [(text, fe_n cx + 1)])
    (EV_check_no_overread + 1 + EV_preset_base64_decode + EV_check_as_written) HB HJ2 HARU2);
  [ rewrite <- app_assoc; cbn [app]; apply (Permutation_trans Hpm); exact Hperm
  | destruct Hcom as (Hk & _); unfold EV_check_as_written in *; lia
  | exact Hbsum ].
+ exists (c_live cx + dec_size (fe_tb cx)). exact Hglob4.
Qed.

(* ---- the segment: the six calls chained ---- *)
Lemma fe_seg6 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_caw [fe_len_atom 46]) (INV_C6 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss PC_C5 [fe_len_lit (-1)]) (INV_C5 B).
Proof.
intros POST HN.
exact (s6_step1 POST (s6_step2 POST (s6_step3 POST (s6_step4 POST (s6_step5 POST (s6_step6 POST HN)))))).
Qed.
End s6.
