(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/YChd.v, with its module paths and module names changed; 90 of its 122 lines of code are new or changed and 513 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0b YP0a.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCkd.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0d YP0c YP07 YI0w YI0z YI12 YC4a YC8i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC80 YC1f YC1g YC1h YC81 YC4b YC44 YC45 YC85 YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC8g YC1i.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YCjr YCj1 YCja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Rt Require Import SnprintfDef.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import ReacDiscoTableJson.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_json_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
#[local] Notation VAL := (@pa_val _ lib_both3_0_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ lib_both3_0_listing PI).
#[local] Notation BASE := (@pa_val _ lib_both3_0_listing PI A_TEXT).
Definition tj_extra (B : asyms) : list word := [Z_to_bv 64 SB; Z_to_bv 64 (as_uar_cell B)].
Definition tj_regions0 : smem :=
[ stack_region 288; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ].
Definition tj_atoms0 : list (nat * afact) :=
[ (2%nat, mkAF (2^46) (2^47) 4); (32%nat, mkAF SB SB 0); (13%nat, mkAF 0 (2^31 - 1) 0) ].
Definition ss_tj_entry : sstate := mkSS AF_both3_reac_disco_table_json sr_atoms tj_regions0 None (mkFacts tj_atoms0 [] []).
Definition ss_tj0 : sstate :=
(mkSS 23520
[SLit 0; SOff 512 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 513 0; SOff 514 0; SOff 515 0; SOff 2 0; SOff 60 0; SLit 18446744073709551608; SLit 3; SLit 18446744073709551603; SOff 278 0; SOff 279 0; SOff 521 0; SOff 522 0; SOff 523 0; SOff 516 0; SOff 516 0; SOff 13 0; SOff 12 0; SOff 529 0; SLit 18446744073709551615; SOff 11 0; SOff 32 0; SOff 26 0; SOff 10 0; SOff 524 0; SOff 525 0; SOff 526 0; SOff 527 0]
[YP09.mkRegion (Some 529%nat) 0 32 0 32 [YP09.mkChunk 27 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 26 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 25 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 24 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 31 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 30 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 29 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 28 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 23 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 22 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 21 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 20 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 19 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 18 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 17 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 16 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551602)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601))];
YP09.mkRegion (Some 516%nat) 0 256 0 256 [YP09.mkChunk 16 (CVal 8 (SOff 279 0)); YP09.mkChunk 8 (CVal 8 (SOff 278 0)); YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 248 (CVal 8 (SOff 528 0))];
YP09.mkRegion (Some 60%nat) 0 184 0 184 [YP09.mkChunk 176 (CVal 8 (SOff 516 0))];
YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0))];
YP09.mkRegion (Some 241%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 253 0))];
YP09.mkRegion (Some 253%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
YP09.mkRegion (Some 242%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))];
YP09.mkRegion (Some 33%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))]]
None
(mkFacts
[(529%nat, mkAF 2147451392 17594333495296 2); (528%nat, mkAF 4096 140737479966720 0); (516%nat, mkAF 4096 140737479966720 5); (60%nat, mkAF 70368744177152 140737488355328 5); (2%nat, mkAF 70368744177664 140737488355328 4); (32%nat, mkAF 2147450880 2147450880 0); (13%nat, mkAF 0 2147483647 0)]
[]
[(SAlu ALU_ADD (SAlu ALU_SRL (SOff 516 0) (SLit 3)) (SOff 32 0), SOff 529 0)])).
Record tjcx := mkTJCX {
c_fq : YK11.FPState;
c_ly : alayout; c_S : astate; c_W : world SEGS; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
c_ch : list (Z * Z * Z);
c_t : Z; c_now : Z; c_buf : Z; c_cap : Z; c_Nb : Z; c_T : list byte;
c_fpos : Z; c_sp1 : Z;
c_E0 : env }.
Definition tj_F (cx : tjcx) : Z := frame_addr (c_ly cx) 2 (c_fpos cx).
Definition tj_FL (cx : tjcx) : Z := flag_addr (c_ly cx) 2 (c_fpos cx).
Section h.
Variable B : asyms.
Variable IMG : world SEGS -> (word -> option byte) -> Prop.
Definition tj_baseX (cx : tjcx) : Prop :=
afn_pre SEGS B REAC_DISCO_TABLE_JSON_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) /\
Z.of_nat (length (frames (c_S cx))) <= 7 /\
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H (c_W cx)) (c_mem cx)) /\
IMG (c_W cx) (c_mem cx) /\
getr (c_regs cx) 10 = w64 (c_t cx) /\ getr (c_regs cx) 11 = w64 (c_now cx) /\
getr (c_regs cx) 12 = w64 (c_buf cx) /\ getr (c_regs cx) 13 = w64 (c_cap cx) /\
0 <= c_now cx < 2 ^ 64 /\ 0 <= c_cap cx < 2 ^ 31 /\
afobj SEGS B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_t cx) 400 /\
garr8 SEGS (mrestrict (w_H (c_W cx)) (c_mem cx)) (c_t cx) (map bv_unsigned (c_T cx)) /\
length (c_T cx) = 400%nat /\ disco_table_c.table_ok (c_T cx) /\
(3 <= c_cap cx -> In (c_buf cx, c_Nb cx) (ablocks B (c_ly cx) (c_S cx)) /\ c_cap cx <= req_size (c_Nb cx)) /\
c_sp1 cx = 32 * ((spZ (c_regs cx) + -288) / 32) /\
(forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (c_E0 cx) n = getr (c_regs cx) r) /\
ew (c_E0 cx) 32 = Z_to_bv 64 SB /\
ew (c_E0 cx) 33 = Z_to_bv 64 (as_uar_cell B) /\
bv_unsigned (ew (c_E0 cx) 2) = spZ (c_regs cx) /\
Z.land (Z.shiftr (bv_unsigned (@fp_csr (c_fq cx))) 5) 7 = 0.
Definition tj_EX (cx : tjcx) (E : env) : Prop :=
(forall n, (n < 34)%nat -> ew E n = ew (c_E0 cx) n) /\
ew E 60 = Z_to_bv 64 (c_sp1 cx) /\ ew E 516 = Z_to_bv 64 (tj_F cx) /\ ew E 528 = Z_to_bv 64 (tj_FL cx) /\
ew E 529 = Z_to_bv 64 (SB + tj_F cx / 8) /\
img_env VAL A_LIM E.
Definition tj_postX (cx : tjcx) : world SEGS -> config -> Prop :=
treac_disco_table_json_post B (c_fq cx) (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
(c_T cx) (c_now cx) (c_buf cx) (c_cap cx).
Definition tj_from0 (ss : sstate)
(INV : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
forall (cx : tjcx) (E : env) (k : Z) ly3 S3 W3 (ms3 : machine_state) md3,
tj_baseX cx -> tj_EX cx E ->
ajournal SEGS B REAC_DISCO_TABLE_JSON_STK (spZ (c_regs cx)) (tj_fp (c_buf cx) (c_cap cx)) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
[(2, c_fpos cx)] ly3 S3 W3 (ms_mem ms3) md3 k ->
frames S3 = (2, c_fpos cx) :: frames (c_S cx) ->
INV cx E k ly3 S3 W3 ms3 md3 ->
st_ok_pi (fx := c_fq cx) SEGS VAL E ss (restrict (w_H W3) ms3) ->
SRr SEGS W3 (mkCfg ms3 md3) (tj_postX cx).
Definition INV_tj0 (kmax : Z) : tjcx -> env -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop :=
fun cx E k ly3 S3 W3 ms3 md3 => k <= kmax /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx).
Lemma tj_EX_havoc : forall cx E N vs, (530 <= N)%nat -> tj_EX cx E -> tj_EX cx (havoc E N vs).
Proof.
intros cx E N vs HN (AG & E60 & E516 & E528 & E529 & HEI). unfold tj_EX. rewrite !ew_havoc_old by lia.
split; [|split; [exact E60 | split; [exact E516 | split; [exact E528 | split; [exact E529 | apply img_env_havoc_hi; [exact HEI | unfold A_LIM; lia]]]]]].
intros n Hn. rewrite !ew_havoc_old by lia. apply AG. exact Hn.
Qed.
Lemma INV_tj0_havoc : forall kmax cx E N vs k ly3 S3 W3 ms3 md3,
INV_tj0 kmax cx E k ly3 S3 W3 ms3 md3 -> INV_tj0 kmax cx (havoc E N vs) k ly3 S3 W3 ms3 md3.
Proof. intros; assumption. Qed.
End h.
End f.
End d.
