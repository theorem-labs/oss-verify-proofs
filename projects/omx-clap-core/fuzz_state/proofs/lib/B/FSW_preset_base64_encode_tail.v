(* preset_base64_encode 0x84700 (preset_file.c:577-608) on fs.asan-ubsan (image B): the LOOP EXIT (0x849b8) and the
   TAIL (0x849bc .. 0x84b24), toward lib/B/FSH_Fn_writer.v's encode_spec. Same names and argument order as image A's
   Section R (lib/A/FSW_preset_base64_encode.v); every numeral and register here is B's.

   What it proves (names and binder order as image A's, lib/A/FSW_preset_base64_encode.v at
   a working branch 0a3016aa4bf / a working branch 6e3b1de9c97).
   - encR_loop_exit: from the loop's exit 0x849b8 with exactly the premises encR_loop's KEXIT hands over
     (len <= 3R + 2, 3R <= len, the invariant, encR_exit_regs ms R, the first R output quads) to encode_spec's
     post. The exit's `bgeu a3,s0,84b24` (0x849b8) splits: 3R >= len, i.e. len = 3R, goes straight to 0x84b24 with
     a1 = q + 4R = q + 4 * ((len + 2) / 3) and the whole b64_enc bs written; otherwise the tail runs.
   - encR_tail: the same from the tail's entry 0x849bc (encR_exit_regs ms R, 0 <= R, 3R < len < 3R + 3), which
     the len < 3 arm of the entry block reaches with R = 0 (0x849a0 `li a3,0`; 0x849a4 `mv a1,a0`; 0x849a8
     `bltu zero,s0,849bc`).
   Both are composed with encR_nul. Their cores are the CPS lemmas encT_loop_exit_k / encT_tail_k, whose last
   hypothesis is encR_nul's premise list over an arbitrary Q (at 0x84b24, a1 = q + 4 * ((len + 2) / 3) =
   q + enc_size len - 1, b64_enc bs in the block, the invariant, s2, sp and encR_kept).
   The tail writes the four last output bytes: for one leftover byte bA, b64c (bA / 4), b64c ((bA mod 4) * 16), '=',
   '='; for two (bA, bB), b64c (bA / 4), b64c ((bA mod 4) * 16 + bB / 16), b64c ((bB mod 16) * 4), '='. The split
   on len - 3R is the engine's stop at 0x849f0 `bgeu a5,s0` (SRr_sym_branch); the second length test 0x84aac reads
   the same operands, so the condition the split added decides it.

   The 11 UBSan deciders of 0x849bc .. 0x84b24 (branches to the `unimp` 0x84b58). Three stop the engine and are
   refuted here by SRr_sym_branch with the lemma of lib/B/FSW_preset_base64_encode_ub.v: 0x849c0 `bltu a2,s1`
   (enc_ub_849c0; the ranges of data + 3R and data overlap), 0x849f8 `bgeu a3,a6` (enc_ub_849f8 with enc_tU_not;
   the engine cannot range an XOR), 0x84a70 `bltu a7,a3` (enc_ub_84a70, its two-byte and one-byte conjuncts with
   enc_U_t1 / enc_tU_i1one; the shifts by 46 / 58 overflow the interval). The engine decides the other eight from
   the state's atom facts and literals (the ub file's lemma beside each states the same arithmetic): 0x849d0 and
   0x849d4 (enc_ub_849d0 / enc_ub_849d4: atom 9 in [4096, PTOP]), 0x84a2c / 0x84ab8 (enc_ub_84a2c / enc_ub_84ab8:
   a4 is the literal G_B64, so `not a7,a4` folds; the index is a shift of an atom in [0, 255] / an `andi 60`),
   0x84a34 / 0x84a7c / 0x84ae4 / 0x84b04 (enc_ub_84a34 / 84a7c / 84ae4 / 84b04: atom 11 + 0..3 in [4096, PTOP + 3]
   against the literal -1).
   The 9 ASan report rows of the tail (map table 4 rows 12-20: the two input bytes 0x849e4 / 0x84a0c, the three table
   seats 0x84a48 / 0x84a90 / 0x84acc, the four output bytes 0x84a5c / 0x84aa4 / 0x84af4 / 0x84b14) are refuted BY
   CONSTRUCTION: every one is an inline shadow check of a byte the token run's shents cover (the output quad on atom
   11, the input bytes on the seats 60 / 70, the table bytes on the seats 100 / 200 / 300), so each run reaches its
   stop TS_running with no obligation and no __asan_report_* edge is taken.

   rule 24: proves function preset_base64_encode (part tail; reuse search: proof-index preset_base64_encode,
   ported from a working branch 402eb5565fc + donor a working branch b96980d72d1)
   Ported from: lib/A/FSW_preset_base64_encode.v at a working branch 402eb5565fc lines 61-86 (the state /
   seat / shent form), 356-443 (enc_round_state: the st_ok of a walk state), 1571-2009 (encR_round_step: the segment
   runs, the seats, the keep chain and the output bytes, the pattern this file follows), 1032-1232 (encR_nul, whose
   premise list the KNUL hypothesis is); lib/B/FSW_preset_base64_encode_loop.v (a working branch
   4478ee7c74e) for encR_exit_regs and the shape encR_loop's KEXIT hands over. Old-B donor
   a working branch b96980d72d1 lib/B/Prog/preset_base64_encode_blocks.v:792-809 (enc_tail_c0), :821-843
   (enc_tail_c1), :845-877 (enc_tail_a), :879-914 (enc_tail_b), :916-941 (enc_tail_b2), :943-970 (enc_tail_d1),
   :972-1007 (enc_tail_d2), :1009-1051 (enc_tail_e), :1093-1117 (enc_tail_list1 / list2), :1119-1247 (enc_tail: the
   step order and the split on len - 3R), :1287-1295 (the exit test 0x849b8). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSupoison FSupoisonU FSH_YC20 FSH_Gen FSW_preset_base64_encode_blocks.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_rres FSW_ret FSW_writer_tbl
FSW_preset_base64_encode_W FSW_preset_base64_encode_R FSW_preset_base64_encode_ub FSW_preset_base64_encode_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* apply a lemma of a closed Section to the hypotheses of the Section below that carry its binders' names: the Local
   Lemmas there restate lib/B/FSW_preset_base64_encode_R.v's at this file's variables, and the argument list each one
   takes is the sublist of the Section's variables its proof used. *)
From Ltac2 Require Ltac2.
Module EncTL2.
Import Ltac2.Ltac2.
Ltac2 rec sec_app (c : constr) : constr :=
  match Constr.Unsafe.kind (Constr.type c) with
  | Constr.Unsafe.Prod b _ =>
      match Constr.Binder.name b with
      | Some id =>
          match Control.case (fun () => Control.hyp id) with
          | Val v => let (h, _) := v in sec_app (Constr.Unsafe.make (Constr.Unsafe.App c [| h |]))
          | Err _ => c
          end
      | None => c
      end
  | _ => c
  end.
Ltac2 sec_exact (c : constr) : unit := let t := sec_app c in exact $t.
Ltac2 sec_exact1 (x : Ltac1.t) : unit :=
  match Ltac1.to_constr x with Some c => sec_exact c | None => Control.throw Not_found end.
Ltac encRapp X := let f := ltac2:(x |- sec_exact1 x) in f X.
End EncTL2.
Ltac encRapp X := EncTL2.encRapp X.

(* ---- the tail's symbolic state (atoms: 8 len, 9 data, 10 q, 11 the output quad q + 4R, 13 j = 3R, 18 the shadow
   base; a4 = x14 is the LITERAL g_b64, which is what makes `not a7,a4` (0x84a28) fold and the three table deciders
   0x84a2c / 0x84a70 / 0x84ab8 range-decidable; 60 / 70 the two leftover input bytes' seats and 100 / 200 / 300 the
   three table seats the runs add). The tail writes the four bytes q + 4R .. q + 4R + 3, which is the whole write
   window of the one region it carries. ---- *)
Definition enc_tgf : list (nat * afact) :=
  [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (9%nat, mkAF 4096 PTOP 0); (11%nat, mkAF 4096 PTOP 0);
   (13%nat, mkAF 0 (2 ^ 27) 0); (8%nat, mkAF 0 (2 ^ 27) 0)].
Definition enc_tregs : list sv := sr_set sr_atoms 14%bv (SLit G_B64).
Definition enc_tout : YP09.region := YP09.mkRegion (Some 11%nat) 0 4 0 4 [].
(* 0x849bc, the tail's entry: the output quad is inside the block (enc_size len = 4R + 5 when 3R < len) *)
Definition enc_tail_ss : sstate := mkSS 0x849bc enc_tregs [enc_tout] None (mkFacts enc_tgf [] []).
(* 0x849b8, the loop's exit: the `bgeu a3,s0` reads no memory, so the state carries no region (with len = 3R the
   quad q + 4R .. q + 4R + 3 would reach past the block, whose last byte is the NUL slot q + 4R) *)
Definition enc_exit_ss : sstate := mkSS 0x849b8 enc_tregs [] None (mkFacts enc_tgf [] []).
Definition enc_tSH : list shent := [mkSHE 11 0 4].
Definition enc_tSH1 : list shent := enc_tSH ++ [mkSHE 60 0 1].
Definition enc_tSH2 : list shent := enc_tSH1 ++ [mkSHE 70 0 1].
Definition enc_tSHb1 : list shent := enc_tSH2 ++ [mkSHE 100 0 1].
Definition enc_tSHb2 : list shent := enc_tSHb1 ++ [mkSHE 200 0 1].
Definition enc_tSHb3 : list shent := enc_tSHb2 ++ [mkSHE 300 0 1].
Definition enc_tSHa1 : list shent := enc_tSH1 ++ [mkSHE 100 0 1].
Definition enc_tSHa2 : list shent := enc_tSHa1 ++ [mkSHE 200 0 1].

(* ---- the tail's three table indices, as the engine builds them from the leftover bytes ---- *)
(* 0x84a20..0x84a24  slli a3,a2,0x10; srli a2,a3,0x12 *)
Lemma enc_tU_i0 : forall E (n : nat) b, ew E n = w64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 16)) (SLit 18)) = b / 4.
Proof.
intros E n b He Hb.
rewrite (enc_U_srl E _ 18 _ ltac:(lia)
  (enc_U_sll E (SOff n 0) 16 b ltac:(lia) (U_atom E n b He ltac:(lia)))).
exact (enc_t0 b Hb).
Qed.

(* 0x84a1c..0x84a68 on the one-byte arm (a6 = 0): or a3,a6,a3; slli a3,a3,0x2e; srli a3,a3,0x3a *)
Lemma enc_tU_i1one : forall E (n : nat) b, ew E n = w64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_OR (SLit 0) (SAlu ALU_SLL (SOff n 0) (SLit 16))) (SLit 46))
       (SLit 58))
  = (b mod 4) * 16.
Proof.
intros E n b He Hb.
assert (Z0 : U E (SLit 0) = 0) by (rewrite U_SLit; reflexivity).
assert (A0 : U E (SAlu ALU_SLL (SOff n 0) (SLit 16)) = Z.shiftl b 16 mod 2 ^ 64)
  by (apply (enc_U_sll E (SOff n 0) 16 b); [lia | apply (U_atom E n b He); lia]).
assert (Hs : Z.shiftl b 16 mod 2 ^ 64 = b * 65536)
  by (rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 16) with 65536; apply Z.mod_small; lia).
assert (AO : U E (SAlu ALU_OR (SLit 0) (SAlu ALU_SLL (SOff n 0) (SLit 16))) = b * 65536).
{ rewrite (enc_U_or E _ _ _ _ Z0 A0), Hs, Z.lor_0_l. apply Z.mod_small. lia. }
rewrite (enc_U_srl E _ 58 _ ltac:(lia) (enc_U_sll E _ 46 _ ltac:(lia) AO)).
exact (enc_t1_one b Hb).
Qed.

(* 0x84ab0..0x84ab4  srli a2,a6,0x6; andi a2,a2,60, over a6 = b << 8 (the engine folds the pair to `slli 2`) *)
Lemma enc_tland60 : forall b, 0 <= b < 256 -> Z.land (Z.shiftl b 2 mod 2 ^ 64) 60 = (b mod 16) * 4.
Proof.
intros b Hb.
exact (brute1_lemma (fun x => Z.land (Z.shiftl x 2 mod 2 ^ 64) 60) (fun x => (x mod 16) * 4)
  ltac:(vm_compute; reflexivity) b Hb).
Qed.

Lemma enc_tU_i2 : forall E (n : nat) b, ew E n = w64 b -> 0 <= b < 256 ->
  U E (SAlu ALU_AND (SAlu ALU_SLL (SOff n 0) (SLit 2)) (SLit 60)) = (b mod 16) * 4.
Proof.
intros E n b He Hb.
rewrite (U_and_lit E _ 60 ltac:(lia)),
  (enc_U_sll E (SOff n 0) 2 b ltac:(lia) (U_atom E n b He ltac:(lia))).
exact (enc_tland60 b Hb).
Qed.

(* `not rd,rs` = `xori rd,rs,-1` (0x849f4 `not a6,s1`) *)
Lemma enc_tU_not : forall E (x : sv) v, U E x = v -> 0 <= v < 2 ^ 64 ->
  U E (SAlu ALU_XOR x (SLit (-1))) = 18446744073709551615 - v.
Proof.
intros E x v Hx Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite Hx, U_SLit.
replace (zcanon (-1)) with 18446744073709551615 by reflexivity.
rewrite (enc_ub_not v Hv). apply zcanon_id. unfold M64. lia.
Qed.

(* `add a2,a4,x` with a4 the literal g_b64 (0x84a38 / 0x84a80 / 0x84abc) *)
Lemma enc_tU_addG : forall E (y : sv) v, U E y = v -> 0 <= v < 64 ->
  U E (SAlu ALU_ADD (SLit G_B64) y) = G_B64 + v.
Proof.
intros E y v Hy Hv. rewrite U_SAlu. cbn [zalu_raw].
rewrite Hy, U_SLit, (zcanon_id G_B64) by (unfold M64, G_B64; lia).
apply zcanon_id. unfold M64, G_B64. lia.
Qed.

(* the register file of the tail: the atoms, with a4 = g_b64 as a literal *)
Lemma enc_tregs_ok : forall (E : env) regs, regs_ok E sr_atoms regs -> getr regs 14 = w64 G_B64 ->
  regs_ok E enc_tregs regs.
Proof.
intros E regs HR H14. apply regs_ok_by_cases. intros r Hr.
cbv [YP01.all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
  [ lazymatch goal with |- _ = sv_denot _ (sr_get enc_tregs ?x) =>
      let v := eval vm_compute in (sr_get enc_tregs x) in
      let w := eval vm_compute in (sr_get sr_atoms x) in
      change (sr_get enc_tregs x) with v;
      first [ cbn [sv_denot]; exact H14
            | rewrite (HR x); change (sr_get sr_atoms x) with w; reflexivity ]
    end
  | ]).
destruct Hr.
Qed.

(* the tail's indices are six-bit *)
Lemma enc_tix : forall b, 0 <= b < 256 ->
  0 <= b / 4 < 64 /\ 0 <= (b mod 4) * 16 < 64 /\ 0 <= (b mod 16) * 4 < 64 /\
  (forall c, 0 <= c < 256 -> 0 <= (b mod 4) * 16 + c / 16 < 64).
Proof.
intros b Hb. split; [lia|]. split; [lia|].
split; [lia|]. intros c Hc. lia.
Qed.

(* the two leftover-byte lists: len = 3R + 1 and len = 3R + 2 (old-B enc_tail_list1 / list2) *)
Lemma enc_tsplit1 : forall (l : list Z) (n : nat), length l = S n -> l = firstn n l ++ [nth n l 0].
Proof.
intros l n. revert l. induction n as [|n IH]; intros l Hl.
- destruct l as [|a [|b t]]; cbn [length] in Hl; try lia. cbn [firstn nth app]. reflexivity.
- destruct l as [|a t]; cbn [length] in Hl; [lia|].
  cbn [firstn nth app]. f_equal. exact (IH t ltac:(lia)).
Qed.

Lemma enc_tsplit2 : forall (l : list Z) (n : nat), length l = S (S n) ->
  l = firstn n l ++ [nth n l 0; nth (S n) l 0].
Proof.
intros l n. revert l. induction n as [|n IH]; intros l Hl.
- destruct l as [|a [|b [|c t]]]; cbn [length] in Hl; try lia. cbn [firstn nth app]. reflexivity.
- destruct l as [|a t]; cbn [length] in Hl; [lia|].
  cbn [firstn nth app]. f_equal. exact (IH t ltac:(lia)).
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair (lib/B/FSH_Base.v FsShadowSyms) and the image facts (lib/B/FSH_Rt.v fs_img_facts), as in
   lib/B/FSW_preset_base64_encode_W.v's Section W *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* ---------------------------------------------------------------------------------------------------------- *)
Section R.
Variable ly0 : alayout.  Variable St0 : astate.  Variable U0 : list (Z * Z).
Variable W0 : world tfibsegs.  Variable mem0 : word -> option byte.  Variable md0 : Model.
Variable regs0 : bvmap 5 word.
Variable lyc : alayout.  Variable Sc : astate.  Variable Wc : world tfibsegs.
Variable memc : word -> option byte.  Variable mdc : Model.
Variable data len q live peak cnt fail kd : Z.
Variable bs : list Z.

Hypothesis HLN : 0 <= len <= 2 ^ 27.
Hypothesis HBS : WriterSpec.bytes_ok bs.
Hypothesis HBSL : Z.of_nat (length bs) = len.
Hypothesis HDLO : 4096 <= data.
Hypothesis HDHI : data + len <= alloc_ceiling.
(* the state after the call *)
Hypothesis HARUc : ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc memc mdc.
Hypothesis HHEADS : fs_heads B lyc Sc (U0 ++ [(q - HEAD, HEAD)]).
Hypothesis HQB : In (q - HEAD, enc_size len + HEAD) (ablocks B lyc Sc).
Hypothesis HAB : ablocks B lyc Sc = ablocks B ly0 St0 ++ [(q - HEAD, enc_size len + HEAD)].
Hypothesis HQ16 : 4096 + HEAD <= q.
(* the input block, when there is one: an ENTRY block, so the call's new block is a different entry of the list *)
Hypothesis HDB : 0 < len -> In (data - HEAD, kd + HEAD) (ablocks B ly0 St0) /\ len <= kd /\ 0 < kd.
(* ---- what the call's entry memory holds (the fuzz_malloc call's post, read at memc) ---- *)
Hypothesis HRBc : fs_rblock tfibsegs B lyc Sc Wc memc q (enc_size len).
Hypothesis HGLOBc : fs_glob tfibsegs Wc memc (live + enc_size len) (Z.max peak (live + enc_size len))
  ((cnt + 1) mod 2 ^ 64) fail.
Hypothesis HTABc : forall v, 0 <= v < 64 ->
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v).
Hypothesis HRATc : range_addressable (aview tfibsegs (w_H Wc) memc) SHADOW_OFF G_B64 65.
Hypothesis HDATc : garr8 tfibsegs (mrestrict (w_H Wc) memc) data bs.
Hypothesis HKEEPc : forall i, 0 <= i < len ->
  mbyte tfibsegs (mrestrict (w_H Wc) memc) (data + i) = mbyte tfibsegs (mrestrict (w_H W0) mem0) (data + i).
(* the entry frame: ra, s0, s1, s2, s3, s4 saved by the prologue, still there after the call *)
Hypothesis HFRAMEc :
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) /\
  val_mem tfibsegs (mrestrict (w_H Wc) memc) (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)).
Hypothesis HSP0 : spZ regs0 mod 16 = 0 /\ alloc_ceiling + STK_preset_base64_encode <= spZ regs0 /\
  spZ regs0 <= 2 ^ 47.
Hypothesis HRA0 : YK0s.ret_ok (getr regs0 1).

(* lib/B/FSW_preset_base64_encode_R.v's and _loop.v's Section R at this section's variables, as the loop file does:
   the definitions are Lets, the lemmas Local Lemmas (a Prop-typed Let would sit in every proof's context). *)
Let encR_out := FSW_preset_base64_encode_R.encR_out len q.
Let encR_agree := FSW_preset_base64_encode_R.encR_agree memc len q.
Let encR_inv := FSW_preset_base64_encode_R.encR_inv B ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc memc len q.
Let encR_kept := FSW_preset_base64_encode_R.encR_kept regs0.
Let encR_Q := FSW_preset_base64_encode_R.encR_Q B ly0 St0 W0 mem0 data len q live peak cnt fail bs.
Let encR_exit_regs := FSW_preset_base64_encode_loop.encR_exit_regs regs0 data len q.

Local Lemma encR_size_pos : 1 <= enc_size len <= 2 ^ 28.
Proof. exact (FSW_preset_base64_encode_R.encR_size_pos len bs HLN HBSL). Qed.
Local Lemma encR_out_facts :
  enc_apart q (q + enc_size len) /\ q + enc_size len <= alloc_ceiling /\
  (forall a, encR_out a -> ~ in_img tfibsegs a).
Proof. exact (FSW_preset_base64_encode_R.encR_out_facts B U0 lyc Sc Wc memc mdc len q bs HLN HBSL HARUc HQB). Qed.
Local Lemma encR_wr_out : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  forall o, 0 <= o < enc_size len -> writable_at tfibsegs (mrestrict (w_H Wc) mem) (q + o).
Proof. exact (FSW_preset_base64_encode_R.encR_wr_out B U0 lyc Sc Wc len q bs HLN HBSL HQB). Qed.
Local Lemma encR_ra_out : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF q (enc_size len).
Proof. exact (FSW_preset_base64_encode_R.encR_ra_out B U0 lyc Sc Wc len q bs HLN HBSL HHEADS HQB). Qed.
Local Lemma encR_ra_in : forall mem md, ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md -> 0 < len ->
  range_addressable (aview tfibsegs (w_H Wc) mem) SHADOW_OFF data len.
Proof. exact (FSW_preset_base64_encode_R.encR_ra_in B ly0 St0 U0 lyc Sc Wc data len q kd bs HLN HHEADS HAB HDB). Qed.
Local Lemma encR_new_block : ~ In (q - HEAD, enc_size len + HEAD) (ablocks B ly0 St0).
Proof. encRapp FSW_preset_base64_encode_R.encR_new_block. Qed.
Local Lemma encR_in_byte : forall mem (j : nat), encR_agree mem -> (j < length bs)%nat ->
  val_mem tfibsegs (mrestrict (w_H Wc) mem) (data + Z.of_nat j) 1 (nth j bs 0) /\ 0 <= nth j bs 0 < 256.
Proof.
exact (FSW_preset_base64_encode_R.encR_in_byte B ly0 St0 U0 regs0 lyc Sc Wc memc mdc
  data len q live peak cnt kd bs HLN HBSL HDLO HDHI HARUc HAB HDB HDATc).
Qed.
Local Lemma encR_in_out : 0 < len -> forall i, data <= i < data + len -> ~ encR_out i.
Proof. encRapp FSW_preset_base64_encode_R.encR_in_out. Qed.
Local Lemma encR_dj : 0 < len -> data + len <= q \/ q + enc_size len <= data.
Proof. encRapp FSW_preset_base64_encode_R.encR_dj. Qed.
Local Lemma encR_in_apart : 0 < len -> enc_apart data (data + len).
Proof.
exact (FSW_preset_base64_encode_R.encR_in_apart B ly0 St0 U0 regs0 lyc Sc Wc memc mdc
  data len q live peak cnt kd bs HARUc HAB HDB).
Qed.
Local Lemma encR_dj_in_tab : 0 < len -> data + len <= G_B64 \/ G_B64 + 65 <= data.
Proof.
exact (FSW_preset_base64_encode_R.encR_dj_in_tab B ly0 St0 U0 regs0 lyc Sc Wc memc mdc
  data len q live peak cnt kd bs HARUc HAB HDB).
Qed.
Local Lemma encR_dj_out_tab : q + enc_size len <= G_B64 \/ G_B64 + 65 <= q.
Proof.
exact (FSW_preset_base64_encode_R.encR_dj_out_tab B U0 regs0 lyc Sc Wc memc mdc
  len q live peak cnt bs HLN HBSL HARUc HQB).
Qed.
Local Lemma encR_tab_keep : forall mem, encR_agree mem ->
  (forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) memc) (G_B64 + v) 1 (WriterSpec.b64c v)) ->
  forall v, 0 <= v < 64 -> val_mem tfibsegs (mrestrict (w_H Wc) mem) (G_B64 + v) 1 (WriterSpec.b64c v).
Proof. exact (FSW_preset_base64_encode_R.encR_tab_keep B U0 lyc Sc Wc memc mdc len q bs HLN HBSL HARUc HQB). Qed.
Local Lemma encR_shent_seat : forall mem (E : env) (n : nat) v, encR_agree mem ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff n 0) = G_B64 + v -> 0 <= v < 64 ->
  shent_ok tfibsegs enc_Bx E (mrestrict (w_H Wc) mem) (mkSHE n 0 1).
Proof. encRapp FSW_preset_base64_encode_R.encR_shent_seat. Qed.
Local Lemma encR_garr8_keep : forall (m m' : word -> option byte) (base : Z) (l : list Z) (X : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  0 <= base -> base + Z.of_nat (length l) <= 2 ^ 64 ->
  (forall i, base <= i < base + Z.of_nat (length l) -> ~ X i) ->
  garr8 tfibsegs m base l -> garr8 tfibsegs m' base l.
Proof. encRapp FSW_preset_base64_encode_R.encR_garr8_keep. Qed.
Local Lemma encR_garr8_app4 : forall (m : word -> option byte) (pre : list Z) (c0 c1 c2 c3 base off : Z),
  garr8 tfibsegs m base pre -> Z.of_nat (length pre) = off -> 0 <= base -> base + off + 4 <= 2 ^ 64 ->
  val_mem tfibsegs m (base + off + 0) 1 c0 -> val_mem tfibsegs m (base + off + 1) 1 c1 ->
  val_mem tfibsegs m (base + off + 2) 1 c2 -> val_mem tfibsegs m (base + off + 3) 1 c3 ->
  0 <= c0 < 256 -> 0 <= c1 < 256 -> 0 <= c2 < 256 -> 0 <= c3 < 256 ->
  garr8 tfibsegs m base (pre ++ [c0; c1; c2; c3]).
Proof. encRapp FSW_preset_base64_encode_R.encR_garr8_app4. Qed.
Local Lemma encR_nul : forall ms md,
  encR_inv (ms_mem ms) md ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q (WriterSpec.b64_enc bs) ->
  ms = mkst (ms_regs ms) (w64 0x84b24) (ms_mem ms) (seg_rom tfibsegs) ->
  getr (ms_regs ms) 10 = w64 q ->
  getr (ms_regs ms) 11 = w64 (q + 4 * ((len + 2) / 3)) ->
  getr (ms_regs ms) 18 = w64 SHADOW_OFF ->
  spZ (ms_regs ms) = spZ regs0 - 48 ->
  (forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 -> z <> 19 -> z <> 20 ->
     getr (ms_regs ms) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z)) ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof. encRapp FSW_preset_base64_encode_R.encR_nul. Qed.

(* the invariant, built and taken apart without unfolding the Let *)
Local Lemma encT_inv_mk : forall mem md,
  ajournal tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP ly0 St0 W0 (unpoison U0 mem0) md0 []
    lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) mem) md EV_preset_base64_encode ->
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  encR_agree mem -> encR_inv mem md.
Proof. intros mem md H1 H2 H3. exact (conj H1 (conj H2 H3)). Qed.
Local Lemma encT_out_in : forall a, q <= a < q + enc_size len -> encR_out a.
Proof. intros a Ha. exact Ha. Qed.
Local Lemma encT_out_out : forall a, encR_out a -> q <= a < q + enc_size len.
Proof. intros a Ha. exact Ha. Qed.

Local Lemma encT_inv_dest : forall mem md, encR_inv mem md ->
  ajournal tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP ly0 St0 W0 (unpoison U0 mem0) md0 []
    lyc Sc Wc (unpoison (U0 ++ [(q - HEAD, HEAD)]) mem) md EV_preset_base64_encode /\
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md /\ encR_agree mem.
Proof. intros mem md H. exact H. Qed.
Local Lemma encT_exit_dest : forall msx (R : Z), encR_exit_regs msx R ->
  getr (ms_regs msx) 8 = w64 len /\ getr (ms_regs msx) 9 = w64 data /\ getr (ms_regs msx) 10 = w64 q /\
  getr (ms_regs msx) 11 = w64 (q + 4 * R) /\ getr (ms_regs msx) 13 = w64 (3 * R) /\
  getr (ms_regs msx) 14 = w64 G_B64 /\ getr (ms_regs msx) 18 = w64 SHADOW_OFF /\
  spZ (ms_regs msx) = spZ regs0 - 48 /\ encR_kept msx.
Proof. intros msx Rx H. exact H. Qed.
Local Lemma encT_kept_mk : forall msx,
  (forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 -> z <> 19 -> z <> 20 ->
     getr (ms_regs msx) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z)) -> encR_kept msx.
Proof. intros msx H. exact H. Qed.
Local Lemma encT_firstn_len : forall (Rx : Z), 0 <= Rx -> 3 * Rx <= len ->
  length (firstn (Z.to_nat (3 * Rx)) bs) = (3 * Z.to_nat Rx)%nat.
Proof. intros Rx H1 H2. rewrite length_firstn. lia. Qed.
Local Lemma encT_len4 : forall (Rx : Z), 0 <= Rx -> 3 * Rx <= len ->
  Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * Rx)) bs))) = 4 * Rx.
Proof. intros Rx H1 H2. rewrite b64_enc_len, (encT_firstn_len Rx H1 H2). lia. Qed.
Local Lemma encT_len_all : Z.of_nat (length (WriterSpec.b64_enc bs)) = enc_size len - 1.
Proof. rewrite b64_enc_len, HBSL. unfold enc_size. lia. Qed.
Local Lemma encT_split1_len : forall (Rx : Z), 0 <= Rx -> len = 3 * Rx + 1 ->
  length bs = S (Z.to_nat (3 * Rx)).
Proof. intros Rx H1 H2. lia. Qed.
Local Lemma encT_split2_len : forall (Rx : Z), 0 <= Rx -> len = 3 * Rx + 2 ->
  length bs = S (S (Z.to_nat (3 * Rx))).
Proof. intros Rx H1 H2. lia. Qed.
Local Lemma encT_kept_use : forall msx, encR_kept msx ->
  forall z, acallee_saved z -> z <> 2 -> z <> 8 -> z <> 9 -> z <> 18 -> z <> 19 -> z <> 20 ->
    getr (ms_regs msx) (Z_to_bv 5 z) = getr regs0 (Z_to_bv 5 z).
Proof. intros msx H. exact H. Qed.
Local Lemma encT_she : forall (W : world tfibsegs) mem (E : env) (n : nat) (b lo hi a k : Z),
  U E enc_Bx = SHADOW_OFF -> U E (SOff n 0) = b ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF a k ->
  a <= b + lo -> b + hi <= a + k -> lo <= hi -> enc_apart (b + lo) (b + hi) ->
  shent_ok tfibsegs enc_Bx E (mrestrict (w_H W) mem) (mkSHE n lo hi).
Proof. encRapp FSW_preset_base64_encode_W.enc_she. Qed.

(* ---- the tail's st_ok at 0x849bc and the exit's at 0x849b8 ---- *)
Local Lemma encT_state : forall (W : world tfibsegs) mem regs (E : env) out j pc,
  regs_ok E sr_atoms regs ->
  getr regs 8 = w64 len -> getr regs 9 = w64 data -> getr regs 11 = w64 out ->
  getr regs 13 = w64 j -> getr regs 14 = w64 G_B64 -> getr regs 18 = w64 SHADOW_OFF ->
  (forall o, 0 <= o < 4 -> writable_at tfibsegs (mrestrict (w_H W) mem) (out + o)) ->
  4096 <= data <= PTOP -> 4096 <= out -> out + 4 <= PTOP -> 0 <= j <= 2 ^ 27 ->
  st_ok tfibsegs E (mkSS pc enc_tregs [enc_tout] None (mkFacts enc_tgf [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs E out j pc HR R8 R9 R11 R13 R14 R18 HWout Hd Ho0 Ho1 Hj.
assert (EW : forall (r : bv 5) (n : nat), sr_get sr_atoms r = SOff n 0 -> ew E n = getr regs r).
{ intros r n Hn. rewrite (HR r), Hn, fsw_SOff0. reflexivity. }
assert (A8 : ew E 8 = w64 len) by (rewrite (EW 8%bv 8%nat ltac:(vm_compute; reflexivity)); exact R8).
assert (A9 : ew E 9 = w64 data) by (rewrite (EW 9%bv 9%nat ltac:(vm_compute; reflexivity)); exact R9).
assert (A11 : ew E 11 = w64 out) by (rewrite (EW 11%bv 11%nat ltac:(vm_compute; reflexivity)); exact R11).
assert (A13 : ew E 13 = w64 j) by (rewrite (EW 13%bv 13%nat ltac:(vm_compute; reflexivity)); exact R13).
assert (A18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EW 18%bv 18%nat ltac:(vm_compute; reflexivity)); exact R18).
assert (U8 : bv_unsigned (ew E 8) = len) by (rewrite A8; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = data)
  by (rewrite A9; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U11 : bv_unsigned (ew E 11) = out)
  by (rewrite A11; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U13 : bv_unsigned (ew E 13) = j) by (rewrite A13; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
     ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact (enc_tregs_ok E regs HR R14)|].
split.
- split; [vm_compute; reflexivity|]. split.
  + constructor; [|constructor].
    unfold enc_tout, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U11. split; [lia|]. split; [unfold PTOP in *; lia|].
    split; [intros o Ho; apply HWout; lia|]. constructor.
  + apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; exact I].
  unfold enc_tgf. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U9, U11, U13, U8. rewrite !Z.pow_0_r.
  unfold PTOP, SHADOW_OFF in *.
  repeat split; try lia; try (apply Z.mod_1_r).
Qed.

Local Lemma encT_exit_state : forall (W : world tfibsegs) mem regs (E : env) out j,
  regs_ok E sr_atoms regs ->
  getr regs 8 = w64 len -> getr regs 9 = w64 data -> getr regs 11 = w64 out ->
  getr regs 13 = w64 j -> getr regs 14 = w64 G_B64 -> getr regs 18 = w64 SHADOW_OFF ->
  4096 <= data <= PTOP -> 4096 <= out <= PTOP -> 0 <= j <= 2 ^ 27 ->
  st_ok tfibsegs E enc_exit_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 0x849b8) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs E out j HR R8 R9 R11 R13 R14 R18 Hd Ho Hj.
assert (EW : forall (r : bv 5) (n : nat), sr_get sr_atoms r = SOff n 0 -> ew E n = getr regs r).
{ intros r n Hn. rewrite (HR r), Hn, fsw_SOff0. reflexivity. }
assert (A8 : ew E 8 = w64 len) by (rewrite (EW 8%bv 8%nat ltac:(vm_compute; reflexivity)); exact R8).
assert (A9 : ew E 9 = w64 data) by (rewrite (EW 9%bv 9%nat ltac:(vm_compute; reflexivity)); exact R9).
assert (A11 : ew E 11 = w64 out) by (rewrite (EW 11%bv 11%nat ltac:(vm_compute; reflexivity)); exact R11).
assert (A13 : ew E 13 = w64 j) by (rewrite (EW 13%bv 13%nat ltac:(vm_compute; reflexivity)); exact R13).
assert (A18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EW 18%bv 18%nat ltac:(vm_compute; reflexivity)); exact R18).
assert (U8 : bv_unsigned (ew E 8) = len) by (rewrite A8; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = data)
  by (rewrite A9; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U11 : bv_unsigned (ew E 11) = out)
  by (rewrite A11; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U13 : bv_unsigned (ew E 13) = j) by (rewrite A13; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
rewrite restrict_mkst_fx. unfold enc_exit_ss, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
     ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact (enc_tregs_ok E regs HR R14)|].
split.
- split; [vm_compute; reflexivity|]. split; [constructor | cbn; exact I].
- split; [|split; exact I].
  unfold enc_tgf. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U18, U9, U11, U13, U8. rewrite !Z.pow_0_r.
  unfold PTOP, SHADOW_OFF in *.
  repeat split; try lia; try (apply Z.mod_1_r).
Qed.

Local Lemma encT_sh_out : forall mem md (E : env) (r4 : Z),
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff 11 0) = q + r4 ->
  0 <= r4 -> r4 + 4 <= enc_size len ->
  shent_ok tfibsegs enc_Bx E (mrestrict (w_H Wc) mem) (mkSHE 11 0 4).
Proof.
intros mem md E r4 HARUx HB H11 H1 H2.
apply (encT_she Wc mem E 11%nat (q + r4) 0 4 q (enc_size len) HB H11
  (encR_ra_out mem md HARUx)); [lia | lia | lia|].
intros x Hx. apply (proj1 encR_out_facts). lia.
Qed.
Local Lemma encT_sh_in : forall mem md (E : env) (n : nat) (p k : Z),
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem md ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff n 0) = p -> p = data + k ->
  0 <= k -> k + 1 <= len ->
  shent_ok tfibsegs enc_Bx E (mrestrict (w_H Wc) mem) (mkSHE n 0 1).
Proof.
intros mem md E n p k HARUx HB Hn Hp H1 H2. rewrite Hp in Hn.
apply (encT_she Wc mem E n (data + k) 0 1 data len HB Hn
  (encR_ra_in mem md HARUx ltac:(lia))); [lia | lia | lia|].
intros x Hx. apply (encR_in_apart ltac:(lia)). lia.
Qed.

(* ---- the write-window obligation of a tail run: the seats are read-only, the output quad is the block's ---- *)
Local Ltac encT_awr Ex :=
  cbn [enc_tail_ss enc_seat add_atom add_cond ss_mem];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]);
  eapply awr_ok_cons_gen with (k := 11%nat);
  [ reflexivity | exact Ex
  | cbn [enc_tout YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; intros a Ha;
    left; right; right; left;
    exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|]; split; [exact encR_new_block|];
    unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
    [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD in *; lia]
  | apply awr_ok_nil ].
(* read an atom through the ewsets a run's tokens and this file's seats add *)
Local Ltac encT_peel k := repeat (rewrite (ew_ewset_other _ _ _ k) by lia).
(* every byte a run may write is in the output quad *)
Local Ltac encT_wr Ex :=
  intros z (rg & Hrin & Hrg); revert Hrg;
  lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrin end;
  cbn [In] in Hrin;
  repeat (destruct Hrin as [<-|Hrin]); try (destruct Hrin);
  intros Hrg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hrg;
  first [ lia | rewrite Ex in Hrg; lia ].
(* a run writes only inside the output quad, so the invariant's agreement survives it *)
Local Ltac encT_agree HFx HAx Ex :=
  intros x Hx;
  rewrite (enc_frame_X _ _ _ _ encR_out HFx); [exact (HAx x Hx) | | exact Hx];
  intros a (rg & Hrin & Hrg); revert Hrg;
  lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrin end;
  cbn [In] in Hrin;
  repeat (destruct Hrin as [<-|Hrin]); try (destruct Hrin);
  intros Hrg; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hrg;
  first [ lia | apply encT_out_in; rewrite Ex in Hrg; lia ].

Lemma encT_tail_k : forall ms md R (Q : world tfibsegs -> config -> Prop),
  0 <= R -> 3 * R < len -> len <= 3 * R + 2 ->
  encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x849bc) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  (forall ms' md',
     encR_inv (ms_mem ms') md' ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q (WriterSpec.b64_enc bs) ->
     ms' = mkst (ms_regs ms') (w64 0x84b24) (ms_mem ms') (seg_rom tfibsegs) ->
     getr (ms_regs ms') 10 = w64 q ->
     getr (ms_regs ms') 11 = w64 (q + 4 * ((len + 2) / 3)) ->
     getr (ms_regs ms') 18 = w64 SHADOW_OFF ->
     spZ (ms_regs ms') = spZ regs0 - 48 ->
     encR_kept ms' ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg ms md) Q.
Proof.
intros ms md R Q HR0 HRlt HRle HINV HX Hms HPRE KNUL.
destruct (encT_inv_dest (ms_mem ms) md HINV) as (HJ & HARU & HA).
destruct (encT_exit_dest ms R HX) as (R8 & R9 & R10 & R11 & R13 & R14 & R18 & Rsp & Rk).
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
assert (HSZ : enc_size len = 4 * R + 5) by (unfold enc_size; lia).
assert (HQ3 : (len + 2) / 3 = R + 1) by (lia).
assert (HBL : Z.of_nat (length bs) = len) by exact HBSL.
(* the first leftover byte *)
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * R)) HA ltac:(lia)) as (VA & BA).
replace (data + Z.of_nat (Z.to_nat (3 * R))) with (data + 3 * R) in VA by lia.
(* the state at 0x849bc *)
assert (HS : st_ok tfibsegs (Ereg (ms_regs ms) ([] : list word)) enc_tail_ss (restrict (w_H Wc) ms)).
{ rewrite Hms. unfold enc_tail_ss.
  apply (encT_state Wc (ms_mem ms) (ms_regs ms) _ (q + 4 * R) (3 * R) 0x849bc);
    first [ apply regs_ok_Ereg | exact R8 | exact R9 | exact R11 | exact R13 | exact R14 | exact R18
          | intros o Ho; replace (q + 4 * R + o) with (q + (4 * R + o)) by lia;
            exact (encR_wr_out (ms_mem ms) md HARU (4 * R + o) ltac:(lia))
          | unfold PTOP in *; lia ]. }
assert (A11 : ew (Ereg (ms_regs ms) ([] : list word)) 11 = w64 (q + 4 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact R11).
assert (A9 : ew (Ereg (ms_regs ms) ([] : list word)) 9 = w64 data)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact R9).
assert (A8e : ew (Ereg (ms_regs ms) ([] : list word)) 8 = w64 len)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact R8).
assert (A13 : ew (Ereg (ms_regs ms) ([] : list word)) 13 = w64 (3 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 13 13%bv eq_refl); exact R13).
assert (A10 : ew (Ereg (ms_regs ms) ([] : list word)) 10 = w64 q)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl); exact R10).
assert (A2 : ew (Ereg (ms_regs ms) ([] : list word)) 2 = getr (ms_regs ms) 2)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); reflexivity).
assert (A18 : ew (Ereg (ms_regs ms) ([] : list word)) 18 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact R18).
assert (E11u : bv_unsigned (ew (Ereg (ms_regs ms) ([] : list word)) 11) = q + 4 * R)
  by (rewrite A11; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (SHOK : sh_ok tfibsegs enc_Bx enc_tSH (Ereg (ms_regs ms) ([] : list word))
  (mrestrict (w_H Wc) (ms_mem ms))).
{ unfold enc_tSH. constructor; [|constructor].
  apply (encT_she Wc (ms_mem ms) _ 11%nat (q + 4 * R) 0 4 q (enc_size len)).
  - apply (U_atom _ 18 SHADOW_OFF A18). unfold SHADOW_OFF. lia.
  - apply (U_atom _ 11 _ A11). unfold PTOP in *. lia.
  - exact (encR_ra_out (ms_mem ms) md HARU).
  - lia.
  - lia.
  - lia.
  - intros x Hx. apply HAPq. lia. }
(* 0x849bc -> 0x849c0: `add a2,s1,a3` *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x849c0.
all: first [ solve [ encT_awr E11u ] | idtac ].
assert (HA0 : encR_agree (ms_mem ms0)) by (encT_agree HF HA E11u).
(* seat 60: a2 = data + 3R, the first leftover byte *)
destruct (encR_in_byte (ms_mem ms0) (Z.to_nat (3 * R)) HA0 ltac:(lia)) as (VA0 & BA0).
replace (data + Z.of_nat (Z.to_nat (3 * R))) with (data + 3 * R) in VA0 by lia.
remember (nth (Z.to_nat (3 * R)) bs 0) as bA eqn:EbA.
destruct (enc_tix bA BA0) as (HI0 & HI1 & HI2 & HI3).
pose proof (b64c_range (bA / 4) ltac:(lia)) as HC0.
pose proof (b64c_range ((bA mod 4) * 16) ltac:(lia)) as HC1.
assert (RA2 : getr (ms_regs ms0) 12 = w64 (data + 3 * R)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply enc_denot_of_U.
  rewrite (enc_U_add2 _ 9 13 0 0 data (3 * R));
    first [ solve [encT_peel 9%nat; exact A9]
          | solve [encT_peel 13%nat; exact A13]
          | solve [unfold PTOP in *; lia] ]. }
(* seat 60 on a2: the byte bA at data + 3R *)
pose proof (enc_seat_ro1 _ _ (restrict (w_H Wc) ms0) 12%bv 60 (data + 3 * R) bA 4096 PTOP HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) RA2 ltac:(lia)
  ltac:(unfold PTOP in *; lia) ltac:(unfold PTOP; lia) ltac:(lia)
  ltac:(cbn [ms_mem restrict]; exact VA0)
  ltac:(apply all_disjoint_of_extents;
        unfold enc_tout, extent_of_region;
        cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
        rewrite (ew_ewset_other _ _ _ 60%nat) by lia; rewrite ew_ewset_same;
        rewrite (ew_ewset_other _ _ _ 11%nat) by lia; rewrite (ew_ewset_other _ _ _ 11%nat) by lia;
        rewrite E11u, (unsigned_lit_small (data + 3 * R)) by (unfold PTOP in *; lia);
        cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
        destruct (encR_dj ltac:(lia)); repeat match goal with |- _ /\ _ => split end;
        try exact I; lia)) as HS1.
(* 0x849c0 `bltu a2,s1`: in[3R] does not wrap below data (enc_ub_849c0) *)
lazymatch type of HS1 with st_ok _ ?EE _ _ =>
  assert (U60 : U EE (SOff 60 0) = data + 3 * R)
    by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | unfold PTOP in *; lia]);
  assert (U9a : U EE (SOff 9 0) = data)
    by (apply (U_atom _ 9%nat); [encT_peel 9%nat; exact A9 | unfold PTOP in *; lia]);
  assert (U18a : U EE enc_Bx = SHADOW_OFF)
    by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
  assert (U11a : U EE (SOff 11 0) = q + 4 * R)
    by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | unfold PTOP in *; lia]);
  assert (E11a : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
end.
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 60 0) (b := SOff 9 0);
  [exact HS1 | intros Hbr HSb | intros Hbr HSb]; rewrite branch_ltu_U, U60, U9a in Hbr.
- rewrite (enc_ub_849c0 data R HR0) in Hbr. discriminate.
- clear HS HS1. rename HSb into HS.
  assert (SHOK1 : sh_ok tfibsegs enc_Bx enc_tSH1
    ltac:(lazymatch type of HS with st_ok _ ?EE _ _ => exact EE end)
    (mrestrict (w_H Wc) (ms_mem ms0))).
  { unfold enc_tSH1, enc_tSH. apply Forall_app. split.
    - constructor; [|constructor].
      exact (encT_sh_out (ms_mem ms0) _ _ (4 * R) HARU U18a U11a ltac:(lia) ltac:(lia)).
    - constructor; [|constructor].
      exact (encT_sh_in (ms_mem ms0) _ _ 60%nat (data + 3 * R) (3 * R) HARU U18a U60 ltac:(lia) ltac:(lia) ltac:(lia)). }
  clear SHOK. rename SHOK1 into SHOK.
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
    mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a
    = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
  { intros a Ha Hx. unfold mbyte.
    rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr
      ltac:(encT_wr E11u) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
    reflexivity. }
  (* 0x849c4 -> 0x849f0: the two null checks, the shadow check of a2 and the load of bA *)
  fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x849f0.
  all: first [ solve [ encT_awr E11a ] | idtac ].
  assert (HA1 : encR_agree (ms_mem ms1)) by (encT_agree HF0 HA0 E11a).
  assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
    mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms1)) a
    = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
  { intros a Ha Hx. rewrite <- (KEEP0 a Ha Hx). unfold mbyte.
    rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr0
      ltac:(encT_wr E11a) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
    reflexivity. }
  lazymatch type of HS with st_ok _ ?EE _ _ =>
    assert (U13b : U EE (SOff 13 1) = 3 * R + 1)
      by (apply (U_atom_off _ 13%nat (3 * R) 1); [encT_peel 13%nat; exact A13 | lia | lia]);
    assert (U8b : U EE (SOff 8 0) = len)
      by (apply (U_atom _ 8%nat); [encT_peel 8%nat; exact A8e | lia]);
    assert (U18b : U EE enc_Bx = SHADOW_OFF)
      by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
    assert (U11b : U EE (SOff 11 0) = q + 4 * R)
      by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | unfold PTOP in *; lia]);
    assert (U60b : U EE (SOff 60 0) = data + 3 * R)
      by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | unfold PTOP in *; lia]);
    assert (E11b : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u);
    assert (E61b : ew EE 61 = w64 bA) by (encT_peel 61%nat; apply ew_ewset_same)
  end.
  (* 0x849f0 `bgeu a5,s0`: one leftover byte (len = 3R + 1) or two (len = 3R + 2) *)
  clear Hbr.
  eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 13 1) (b := SOff 8 0);
    [exact HS | intros Hbr HSb2 | intros Hbr HSb2];
    rewrite branch_geu_U, U13b, U8b in Hbr;
    [apply negb_true_iff, Z.ltb_ge in Hbr | apply negb_false_iff, Z.ltb_lt in Hbr].
  + (* len = 3R + 1: one leftover byte *)
    assert (HL1 : len = 3 * R + 1) by lia.
    clear HS. rename HSb2 into HS.
    (* 0x84a1c -> 0x84a3c: a6 := 0, the first table index (UBSan 0x84a2c / 0x84a34 decided by the engine) *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84a3c.
    all: first [ solve [ encT_awr E11b ] | idtac ].
    assert (HA2 : encR_agree (ms_mem ms2)) by (encT_agree HF1 HA1 E11b).
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms2)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP1 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr1
        ltac:(encT_wr E11b) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    (* seat 100: g_b64 + bA / 4 *)
    assert (RT0 : getr (ms_regs ms2) 12 = w64 (G_B64 + bA / 4)).
    { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms2 12%bv HS).
      lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
      apply enc_denot_of_U. apply (enc_tU_addG _ _ (bA / 4));
        [ apply (enc_tU_i0 _ 61%nat bA); [encT_peel 61%nat; exact E61b | lia]
        | lia ]. }
    pose proof (enc_seat_ro1 _ _ (restrict (w_H Wc) ms2) 12%bv 100 (G_B64 + bA / 4)
      (WriterSpec.b64c (bA / 4)) G_B64 (G_B64 + 63) HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) RT0
      ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia)
      ltac:(pose proof (b64c_range (bA / 4) ltac:(lia)); lia)
      ltac:(cbn [ms_mem restrict];
            exact (encR_tab_keep (ms_mem ms2) HA2 HTABc (bA / 4) ltac:(lia)))
      ltac:(apply all_disjoint_of_extents;
            unfold enc_tout, extent_of_region;
            cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
            encT_peel 100%nat; rewrite ew_ewset_same;
            encT_peel 60%nat; rewrite ew_ewset_same;
            encT_peel 11%nat; rewrite E11u;
            rewrite (unsigned_lit_small (G_B64 + bA / 4)) by (unfold G_B64; lia);
            rewrite (unsigned_lit_small (data + 3 * R)) by (unfold PTOP in *; lia);
            cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
            destruct (encR_dj_in_tab ltac:(lia)); destruct encR_dj_out_tab;
            repeat match goal with |- _ /\ _ => split end; try exact I;
            unfold G_B64 in *; lia)) as HS2.
    clear HS. rename HS2 into HS.
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (U18c : U EE enc_Bx = SHADOW_OFF)
        by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
      assert (U11c : U EE (SOff 11 0) = q + 4 * R)
        by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | unfold PTOP in *; lia]);
      assert (U60c : U EE (SOff 60 0) = data + 3 * R)
        by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | unfold PTOP in *; lia]);
      assert (U100c : U EE (SOff 100 0) = G_B64 + bA / 4)
        by (apply (U_atom _ 100%nat); [encT_peel 100%nat; apply ew_ewset_same
                                      | unfold G_B64; lia]);
      assert (E11c : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u);
      assert (E61c : ew EE 61 = w64 bA) by (encT_peel 61%nat; apply ew_ewset_same)
    end.
    assert (SHOK2 : sh_ok tfibsegs enc_Bx enc_tSHa1
      ltac:(lazymatch type of HS with st_ok _ ?EE _ _ => exact EE end)
      (mrestrict (w_H Wc) (ms_mem ms2))).
    { unfold enc_tSHa1, enc_tSH1, enc_tSH. apply Forall_app. split.
      - apply Forall_app. split.
        + constructor; [|constructor].
          exact (encT_sh_out (ms_mem ms2) _ _ (4 * R) HARU U18c U11c ltac:(lia) ltac:(lia)).
        + constructor; [|constructor].
          exact (encT_sh_in (ms_mem ms2) _ _ 60%nat (data + 3 * R) (3 * R) HARU U18c U60c ltac:(lia) ltac:(lia) ltac:(lia)).
      - constructor; [|constructor].
        exact (encR_shent_seat (ms_mem ms2) _ 100%nat (bA / 4) HA2 U18c U100c
          ltac:(lia)). }
    clear SHOK. rename SHOK2 into SHOK.
    (* 0x84a3c -> 0x84a70: the seat's byte, the store of c0 and the second index *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84a84.
    all: first [ solve [ encT_awr E11c ] | idtac ].
    assert (HA3 : encR_agree (ms_mem ms3)) by (encT_agree HF2 HA2 E11c).
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP2 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr2
        ltac:(encT_wr E11c) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (E61d : ew EE 61 = w64 bA) by (encT_peel 61%nat; apply ew_ewset_same);
      assert (E11d : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
    end.
    (* 0x84a70 `bltu a7,a3`: g_b64 + the second index does not wrap (enc_ub_84a70) *)
    eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 18446744073709416351)
      (b := SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_OR (SLit 0) (SAlu ALU_SLL (SOff 61 0) (SLit 16)))
              (SLit 46)) (SLit 58));
      [exact HS | intros Hbr2 HSb3 | intros Hbr2 HSb3];
      rewrite branch_ltu_U, U_SLit, (zcanon_id 18446744073709416351) in Hbr2 by (unfold M64; lia);
      rewrite (enc_tU_i1one _ 61%nat bA E61d BA0) in Hbr2.
    * rewrite (proj2 (enc_ub_84a70 bA 0 BA0 ltac:(lia))) in Hbr2. discriminate.
    * clear HS. rename HSb3 into HS.
      (* 0x84a74 -> 0x84a84: the second seat's address *)
      fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84a84.
      all: first [ solve [ encT_awr E11d ] | idtac ].
      assert (HA4 : encR_agree (ms_mem ms4)) by (encT_agree HF3 HA3 E11d).
      assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
        mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a
        = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
      { intros a Ha Hx. rewrite <- (KEEP3 a Ha Hx). unfold mbyte.
        rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr3
          ltac:(encT_wr E11d) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
        reflexivity. }
      (* the first table seat is done with: drop it, and seat 200 on g_b64 + (bA mod 4) * 16 *)
      pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(cbn [ss_mem]; reflexivity)) as HSd.
      assert (RT1 : getr (ms_regs ms4) 13 = w64 (G_B64 + (bA mod 4) * 16)).
      { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms4 13%bv HS).
        lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
        apply enc_denot_of_U. apply (enc_tU_addG _ _ ((bA mod 4) * 16));
          [ apply (enc_tU_i1one _ 61%nat bA); [encT_peel 61%nat; apply ew_ewset_same | lia]
          | lia ]. }
      pose proof (enc_seat_ro1 _ _ (restrict (w_H Wc) ms4) 13%bv 200 (G_B64 + (bA mod 4) * 16)
        (WriterSpec.b64c ((bA mod 4) * 16)) G_B64 (G_B64 + 63) HSd
        ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) RT1
        ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia)
        ltac:(pose proof (b64c_range ((bA mod 4) * 16) ltac:(lia)); lia)
        ltac:(cbn [ms_mem restrict];
              exact (encR_tab_keep (ms_mem ms4) HA4 HTABc ((bA mod 4) * 16)
                ltac:(lia)))
        ltac:(apply all_disjoint_of_extents;
              unfold enc_tout, extent_of_region;
              cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
              encT_peel 200%nat; rewrite ew_ewset_same;
              encT_peel 60%nat; rewrite ew_ewset_same;
              encT_peel 11%nat; rewrite E11u;
              rewrite (unsigned_lit_small (G_B64 + (bA mod 4) * 16)) by (unfold G_B64; lia);
              rewrite (unsigned_lit_small (data + 3 * R)) by (unfold PTOP in *; lia);
              cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
              destruct (encR_dj_in_tab ltac:(lia)); destruct encR_dj_out_tab;
              repeat match goal with |- _ /\ _ => split end; try exact I;
              unfold G_B64 in *; lia)) as HS3.
      clear HS HSd. rename HS3 into HS.
      lazymatch type of HS with st_ok _ ?EE _ _ =>
        assert (U18f : U EE enc_Bx = SHADOW_OFF)
          by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
        assert (U11f : U EE (SOff 11 0) = q + 4 * R)
          by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | unfold PTOP in *; lia]);
        assert (U60f : U EE (SOff 60 0) = data + 3 * R)
          by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | unfold PTOP in *; lia]);
        assert (U100f : U EE (SOff 100 0) = G_B64 + bA / 4)
          by (apply (U_atom _ 100%nat); [encT_peel 100%nat; apply ew_ewset_same
                                        | unfold G_B64; lia]);
        assert (U200f : U EE (SOff 200 0) = G_B64 + (bA mod 4) * 16)
          by (apply (U_atom _ 200%nat); [encT_peel 200%nat; apply ew_ewset_same
                                        | unfold G_B64; lia]);
        assert (E11f : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
      end.
      assert (SHOK3 : sh_ok tfibsegs enc_Bx enc_tSHa2
        ltac:(lazymatch type of HS with st_ok _ ?EE _ _ => exact EE end)
        (mrestrict (w_H Wc) (ms_mem ms4))).
      { unfold enc_tSHa2, enc_tSHa1, enc_tSH1, enc_tSH. apply Forall_app. split.
        - apply Forall_app. split.
          + apply Forall_app. split.
            * constructor; [|constructor].
              exact (encT_sh_out (ms_mem ms4) _ _ (4 * R) HARU U18f U11f ltac:(lia) ltac:(lia)).
            * constructor; [|constructor].
              exact (encT_sh_in (ms_mem ms4) _ _ 60%nat (data + 3 * R) (3 * R) HARU U18f U60f ltac:(lia) ltac:(lia) ltac:(lia)).
          + constructor; [|constructor].
            exact (encR_shent_seat (ms_mem ms4) _ 100%nat (bA / 4) HA4 U18f U100f
              ltac:(lia)).
        - constructor; [|constructor].
          exact (encR_shent_seat (ms_mem ms4) _ 200%nat ((bA mod 4) * 16) HA4 U18f U200f
            ltac:(lia)). }
      clear SHOK. rename SHOK3 into SHOK.
      (* 0x84a84 -> 0x84b24: the store of c1, the two '=' and the fourth output byte *)
      fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84b24.
      all: first [ solve [ encT_awr E11f ] | idtac ].
      assert (HA5 : encR_agree (ms_mem ms5)) by (encT_agree HF4 HA4 E11f).
      assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
        mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) a
        = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
      { intros a Ha Hx. rewrite <- (KEEP4 a Ha Hx). unfold mbyte.
        rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr4
          ltac:(encT_wr E11f) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
        reflexivity. }
      (* the four bytes the tail stored, read off the output region's chunks *)
      pose proof (fsw_region_nth _ _ (restrict (w_H Wc) ms5) 2
        (YP09.mkRegion (Some 11%nat) 0 4 0 4
           [YP09.mkChunk 3 (CVal 1 (SLit 61)); YP09.mkChunk 2 (CVal 1 (SLit 61));
            YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))])
        HS ltac:(cbn [ss_mem nth_error]; reflexivity)) as HRout.
      cbn [ms_mem restrict] in HRout.
      lazymatch type of HS with st_ok _ ?EE _ _ =>
        assert (E11g : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u);
        assert (VQ : forall (od : Z) (e : sv) (v : Z),
          In (YP09.mkChunk od (CVal 1 e))
             [YP09.mkChunk 3 (CVal 1 (SLit 61)); YP09.mkChunk 2 (CVal 1 (SLit 61));
              YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))] ->
          sv_denot EE e = Z_to_bv 64 v -> 0 <= v < 256 ->
          val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) (q + 4 * R + od) 1 v)
        by (intros od e v Hin Hd Hv;
            exact (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 od 1%N e v HRout E11g Hin Hd
              ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)))
      end.
      assert (VO0 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) (q + 4 * R + 0) 1
        (WriterSpec.b64c (bA / 4)))
        by (apply (VQ 0 (SOff 101 0)); [cbn; tauto
            | rewrite fsw_SOff0; encT_peel 101%nat; apply ew_ewset_same | lia]).
      assert (VO1 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) (q + 4 * R + 1) 1
        (WriterSpec.b64c ((bA mod 4) * 16)))
        by (apply (VQ 1 (SOff 201 0)); [cbn; tauto
            | rewrite fsw_SOff0; encT_peel 201%nat; apply ew_ewset_same | lia]).
      assert (VO2 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) (q + 4 * R + 2) 1 61)
        by (apply (VQ 2 (SLit 61)); [cbn; tauto
            | apply enc_denot_of_U; rewrite U_SLit; reflexivity | lia]).
      assert (VO3 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) (q + 4 * R + 3) 1 61)
        by (apply (VQ 3 (SLit 61)); [cbn; tauto
            | apply enc_denot_of_U; rewrite U_SLit; reflexivity | lia]).
      (* the model: one leftover byte is encoded as two letters and two '=' *)
      assert (HLEN4 : Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs))) = 4 * R)
        by exact (encT_len4 R ltac:(lia) ltac:(lia)).
      assert (HMOD : WriterSpec.b64_enc bs
        = WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)
          ++ [WriterSpec.b64c (bA / 4); WriterSpec.b64c ((bA mod 4) * 16); 61; 61]).
      { rewrite (enc_tsplit1 bs (Z.to_nat (3 * R)) (encT_split1_len R ltac:(lia) HL1)) at 1.
        rewrite (b64_enc_app (Z.to_nat R) _ _ (encT_firstn_len R ltac:(lia) ltac:(lia))).
        rewrite <- EbA. cbn [WriterSpec.b64_enc]. reflexivity. }
      assert (HPRE5 : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) q (WriterSpec.b64_enc bs)).
      { rewrite HMOD. apply (encR_garr8_app4 _ _ _ _ _ _ q (4 * R));
          first [ solve [apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q _
                           (fun x => q + 4 * R <= x < q + 4 * R + 4) KEEP5 ltac:(lia)
                           ltac:(rewrite HLEN4; lia) ltac:(intros i Hi; rewrite HLEN4 in Hi; lia) HPRE)]
                | solve [exact HLEN4] | solve [lia] | solve [exact VO0] | solve [exact VO1]
                | solve [exact VO2] | solve [exact VO3] ]. }
      (* the hand-off at 0x84b24 *)
      apply (KNUL ms5 _);
        [ exact (encT_inv_mk (ms_mem ms5) _ HJ HARU HA5)
        | exact HPRE5
        | pose proof (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms5 HS ltac:(cbn [ss_resv]; reflexivity)) as HPC;
          lazymatch type of HPC with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
            let pc' := eval vm_compute in pc in change pc with pc' in HPC end;
          exact HPC
        | exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
                   ltac:(encT_peel 10%nat; rewrite A10; apply unsigned_lit_small; lia)
                   ltac:(lia))
        | rewrite HQ3; replace (q + 4 * (R + 1)) with (q + 4 * R + 4) by lia;
          exact (enc_reg_val _ _ _ _ 11%bv 11 4 (q + 4 * R) HS ltac:(vm_compute; reflexivity)
                   ltac:(encT_peel 11%nat; exact E11u) ltac:(lia))
        | exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
                   ltac:(encT_peel 18%nat; rewrite A18; apply unsigned_lit_small;
                         unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))
        | unfold spZ; rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
            ltac:(vm_compute; reflexivity) ltac:(encT_peel 2%nat; rewrite A2; reflexivity)
            ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia));
          unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small;
            [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
             pose proof (u64_range (getr (ms_regs ms) 2)); lia]
        | apply encT_kept_mk; intros z Hz Hz2 Hz8 Hz9 Hz18 Hz19 Hz20;
          assert (HZ : z = 3 \/ z = 4 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26
                       \/ z = 27) by (unfold acallee_saved in Hz; lia);
          destruct HZ as [HE|[HE|[HE|[HE|[HE|[HE|[HE|[HE|HE]]]]]]]]; subst z;
          (lazymatch goal with |- getr (ms_regs ?mx) ?rx = _ =>
             rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ mx rx HS) end;
           lazymatch goal with |- sv_denot _ ?t = _ =>
             let t' := eval vm_compute in t in change t with t' end;
           rewrite fsw_SOff0;
           lazymatch goal with |- ew _ ?n = _ => encT_peel n end;
           lazymatch goal with |- ew _ ?n = getr _ ?r =>
             rewrite (ew_Ereg_nat (ms_regs ms) ([] : list word) n r
               ltac:(vm_compute; reflexivity)) end;
           apply (encT_kept_use ms Rk); solve [unfold acallee_saved; lia | lia]) ].
  + (* len = 3R + 2: two leftover bytes *)
    assert (HL2 : len = 3 * R + 2) by lia.
    clear HS. rename HSb2 into HS.
    destruct (encR_in_byte (ms_mem ms1) (Z.to_nat (3 * R + 1)) HA1 ltac:(lia)) as (VB1 & BB1).
    replace (data + Z.of_nat (Z.to_nat (3 * R + 1))) with (data + 3 * R + 1) in VB1 by lia.
    remember (nth (Z.to_nat (3 * R + 1)) bs 0) as bB eqn:EbB.
    destruct (enc_tix bB BB1) as (_ & _ & HJ2 & _).
    pose proof (HI3 bB BB1) as HJ1.
    pose proof (b64c_range ((bA mod 4) * 16 + bB / 16) ltac:(lia)) as HC1'.
    pose proof (b64c_range ((bB mod 16) * 4) ltac:(lia)) as HC2'.
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (U9g : U EE (SOff 9 0) = data)
        by (apply (U_atom _ 9%nat); [encT_peel 9%nat; exact A9 | lia]);
      assert (U13g : U EE (SOff 13 0) = 3 * R)
        by (apply (U_atom _ 13%nat); [encT_peel 13%nat; exact A13 | lia])
    end.
    (* 0x849f4 `not a6,s1`; 0x849f8 `bgeu a3,a6`: data + 3R + 1 does not wrap (enc_ub_849f8) *)
    eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 13 0)
      (b := SAlu ALU_XOR (SOff 9 0) (SLit (-1)));
      [exact HS | intros Hbr3 HSb4 | intros Hbr3 HSb4];
      rewrite branch_geu_U, U13g, (enc_tU_not _ (SOff 9 0) data U9g ltac:(lia)) in Hbr3;
      rewrite (enc_ub_849f8 data len R HDHI ltac:(lia) ltac:(lia)) in Hbr3.
    { cbn [negb] in Hbr3. discriminate. }
    clear HS. rename HSb4 into HS.
    (* 0x849fc -> 0x84a00: s1 := data + 3R + 1 *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84a00.
    all: first [ solve [ encT_awr E11b ] | idtac ].
    assert (HA2 : encR_agree (ms_mem ms2)) by (encT_agree HF1 HA1 E11b).
    assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms2)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP1 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr1
        ltac:(encT_wr E11b) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    (* seat 70 on s1: the byte bB at data + 3R + 1 *)
    destruct (encR_in_byte (ms_mem ms2) (Z.to_nat (3 * R + 1)) HA2 ltac:(lia)) as (VB2 & _).
    replace (data + Z.of_nat (Z.to_nat (3 * R + 1))) with (data + 3 * R + 1) in VB2 by lia.
    rewrite <- EbB in VB2.
    assert (RB : getr (ms_regs ms2) 9 = w64 (data + 3 * R + 1)).
    { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms2 9%bv HS).
      lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
      apply enc_denot_of_U.
      rewrite (enc_U_add2 _ 9 13 1 0 data (3 * R));
        first [ solve [encT_peel 9%nat; exact A9] | solve [encT_peel 13%nat; exact A13]
              | solve [lia] ]. }
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (E11h : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
    end.
    pose proof (enc_seat_ro1 _ _ (restrict (w_H Wc) ms2) 9%bv 70 (data + 3 * R + 1) bB 4096 PTOP HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) RB ltac:(lia)
      ltac:(unfold PTOP; lia) ltac:(unfold PTOP; lia) ltac:(lia)
      ltac:(cbn [ms_mem restrict]; exact VB2)
      ltac:(apply all_disjoint_of_extents;
            unfold enc_tout, extent_of_region;
            cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
            encT_peel 70%nat; rewrite ew_ewset_same;
            encT_peel 60%nat; rewrite ew_ewset_same;
            encT_peel 11%nat; rewrite E11u;
            rewrite (unsigned_lit_small (data + 3 * R + 1)) by lia;
            rewrite (unsigned_lit_small (data + 3 * R)) by lia;
            cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
            destruct (encR_dj ltac:(lia)); repeat match goal with |- _ /\ _ => split end;
            try exact I; lia)) as HS2.
    clear HS. rename HS2 into HS.
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (U18h : U EE enc_Bx = SHADOW_OFF)
        by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
      assert (U11h : U EE (SOff 11 0) = q + 4 * R)
        by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | lia]);
      assert (U60h : U EE (SOff 60 0) = data + 3 * R)
        by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | lia]);
      assert (U70h : U EE (SOff 70 0) = data + 3 * R + 1)
        by (apply (U_atom _ 70%nat); [encT_peel 70%nat; apply ew_ewset_same | lia]);
      assert (E11i : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
    end.
    assert (SHOK2 : sh_ok tfibsegs enc_Bx enc_tSH2
      ltac:(lazymatch type of HS with st_ok _ ?EE _ _ => exact EE end)
      (mrestrict (w_H Wc) (ms_mem ms2))).
    { unfold enc_tSH2, enc_tSH1, enc_tSH. apply Forall_app. split.
      - apply Forall_app. split.
        + constructor; [|constructor].
          exact (encT_sh_out (ms_mem ms2) _ _ (4 * R) HARU U18h U11h ltac:(lia) ltac:(lia)).
        + constructor; [|constructor].
          exact (encT_sh_in (ms_mem ms2) _ _ 60%nat (data + 3 * R) (3 * R) HARU U18h U60h ltac:(lia) ltac:(lia) ltac:(lia)).
      - constructor; [|constructor].
        exact (encT_sh_in (ms_mem ms2) _ _ 70%nat (data + 3 * R + 1) (3 * R + 1) HARU U18h U70h ltac:(lia) ltac:(lia) ltac:(lia)). }
    clear SHOK. rename SHOK2 into SHOK.
    (* 0x84a00 -> 0x84a3c: the shadow check and the load of bB, then the first table index *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84a3c.
    all: first [ solve [ encT_awr E11i ] | idtac ].
    assert (HA3 : encR_agree (ms_mem ms3)) by (encT_agree HF2 HA2 E11i).
    assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms3)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP2 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr2
        ltac:(encT_wr E11i) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    (* seat 100: g_b64 + bA / 4 *)
    assert (RT0 : getr (ms_regs ms3) 12 = w64 (G_B64 + bA / 4)).
    { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms3 12%bv HS).
      lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
      apply enc_denot_of_U. apply (enc_tU_addG _ _ (bA / 4));
        [ apply (enc_tU_i0 _ 61%nat bA); [encT_peel 61%nat; apply ew_ewset_same | lia] | lia ]. }
    pose proof (enc_seat_ro1 _ _ (restrict (w_H Wc) ms3) 12%bv 100 (G_B64 + bA / 4)
      (WriterSpec.b64c (bA / 4)) G_B64 (G_B64 + 63) HS
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) RT0
      ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(lia)
      ltac:(cbn [ms_mem restrict]; exact (encR_tab_keep (ms_mem ms3) HA3 HTABc (bA / 4) ltac:(lia)))
      ltac:(apply all_disjoint_of_extents;
            unfold enc_tout, extent_of_region;
            cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
            encT_peel 100%nat; rewrite ew_ewset_same;
            encT_peel 70%nat; rewrite ew_ewset_same;
            encT_peel 60%nat; rewrite ew_ewset_same;
            encT_peel 11%nat; rewrite E11u;
            rewrite (unsigned_lit_small (G_B64 + bA / 4)) by (unfold G_B64; lia);
            rewrite (unsigned_lit_small (data + 3 * R + 1)) by lia;
            rewrite (unsigned_lit_small (data + 3 * R)) by lia;
            cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
            destruct (encR_dj_in_tab ltac:(lia)); destruct encR_dj_out_tab;
            repeat match goal with |- _ /\ _ => split end; try exact I;
            unfold G_B64 in *; lia)) as HS3.
    clear HS. rename HS3 into HS.
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (U18j : U EE enc_Bx = SHADOW_OFF)
        by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
      assert (U11j : U EE (SOff 11 0) = q + 4 * R)
        by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | lia]);
      assert (U60j : U EE (SOff 60 0) = data + 3 * R)
        by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | lia]);
      assert (U70j : U EE (SOff 70 0) = data + 3 * R + 1)
        by (apply (U_atom _ 70%nat); [encT_peel 70%nat; apply ew_ewset_same | lia]);
      assert (U100j : U EE (SOff 100 0) = G_B64 + bA / 4)
        by (apply (U_atom _ 100%nat); [encT_peel 100%nat; apply ew_ewset_same
                                      | unfold G_B64; lia]);
      assert (E11j : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u);
      assert (E61j : ew EE 61 = w64 bA) by (encT_peel 61%nat; apply ew_ewset_same);
      assert (E71j : ew EE 71 = w64 bB) by (encT_peel 71%nat; apply ew_ewset_same)
    end.
    assert (SHOK3 : sh_ok tfibsegs enc_Bx enc_tSHb1
      ltac:(lazymatch type of HS with st_ok _ ?EE _ _ => exact EE end)
      (mrestrict (w_H Wc) (ms_mem ms3))).
    { unfold enc_tSHb1, enc_tSH2, enc_tSH1, enc_tSH. apply Forall_app. split.
      - apply Forall_app. split.
        + apply Forall_app. split.
          * constructor; [|constructor].
            exact (encT_sh_out (ms_mem ms3) _ _ (4 * R) HARU U18j U11j ltac:(lia) ltac:(lia)).
          * constructor; [|constructor].
            exact (encT_sh_in (ms_mem ms3) _ _ 60%nat (data + 3 * R) (3 * R) HARU U18j U60j ltac:(lia) ltac:(lia) ltac:(lia)).
        + constructor; [|constructor].
          exact (encT_sh_in (ms_mem ms3) _ _ 70%nat (data + 3 * R + 1) (3 * R + 1) HARU U18j U70j ltac:(lia) ltac:(lia) ltac:(lia)).
      - constructor; [|constructor].
        exact (encR_shent_seat (ms_mem ms3) _ 100%nat (bA / 4) HA3 U18j U100j ltac:(lia)). }
    clear SHOK. rename SHOK3 into SHOK.
    (* 0x84a3c -> 0x84a70: the seat's byte, the store of c0 and the second index *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84a84.
    all: first [ solve [ encT_awr E11j ] | idtac ].
    assert (HA4 : encR_agree (ms_mem ms4)) by (encT_agree HF3 HA3 E11j).
    assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP3 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr3
        ltac:(encT_wr E11j) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (E61k : ew EE 61 = w64 bA) by (encT_peel 61%nat; apply ew_ewset_same);
      assert (E71k : ew EE 71 = w64 bB) by (encT_peel 71%nat; apply ew_ewset_same);
      assert (E11k : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
    end.
    (* 0x84a70 `bltu a7,a3`: g_b64 + the second index does not wrap (enc_ub_84a70) *)
    eapply SRr_sym_branch with (c := BC_LTU) (a := SLit 18446744073709416351)
      (b := SAlu ALU_SRL (SAlu ALU_SLL
              (SAlu ALU_OR (SAlu ALU_SLL (SOff 71 0) (SLit 8)) (SAlu ALU_SLL (SOff 61 0) (SLit 16)))
              (SLit 46)) (SLit 58));
      [exact HS | intros Hbr4 HSb5 | intros Hbr4 HSb5];
      rewrite branch_ltu_U, U_SLit, (zcanon_id 18446744073709416351) in Hbr4 by (unfold M64; lia);
      rewrite (enc_U_t1 _ 61%nat 71%nat bA bB E61k E71k BA0 BB1) in Hbr4.
    { rewrite (proj1 (enc_ub_84a70 bA bB BA0 BB1)) in Hbr4. discriminate. }
    clear HS. rename HSb5 into HS.
    (* 0x84a74 -> 0x84a84: the second seat's address *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84a84.
    all: first [ solve [ encT_awr E11k ] | idtac ].
    assert (HA5 : encR_agree (ms_mem ms5)) by (encT_agree HF4 HA4 E11k).
    assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP4 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr4
        ltac:(encT_wr E11k) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    (* drop the first table seat and seat 200 on g_b64 + the second index *)
    pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(cbn [ss_mem]; reflexivity)) as HSd.
    assert (RT1 : getr (ms_regs ms5) 13 = w64 (G_B64 + ((bA mod 4) * 16 + bB / 16))).
    { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms5 13%bv HS).
      lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
      apply enc_denot_of_U. apply (enc_tU_addG _ _ ((bA mod 4) * 16 + bB / 16));
        [ apply (enc_U_t1 _ 61%nat 71%nat bA bB);
          first [ solve [encT_peel 61%nat; apply ew_ewset_same]
                | solve [encT_peel 71%nat; apply ew_ewset_same] | solve [lia] ]
        | lia ]. }
    pose proof (enc_seat_ro1 _ _ (restrict (w_H Wc) ms5) 13%bv 200
      (G_B64 + ((bA mod 4) * 16 + bB / 16)) (WriterSpec.b64c ((bA mod 4) * 16 + bB / 16))
      G_B64 (G_B64 + 63) HSd
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) RT1
      ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(lia)
      ltac:(cbn [ms_mem restrict];
            exact (encR_tab_keep (ms_mem ms5) HA5 HTABc ((bA mod 4) * 16 + bB / 16) ltac:(lia)))
      ltac:(apply all_disjoint_of_extents;
            unfold enc_tout, extent_of_region;
            cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
            encT_peel 200%nat; rewrite ew_ewset_same;
            encT_peel 70%nat; rewrite ew_ewset_same;
            encT_peel 60%nat; rewrite ew_ewset_same;
            encT_peel 11%nat; rewrite E11u;
            rewrite (unsigned_lit_small (G_B64 + ((bA mod 4) * 16 + bB / 16)))
              by (unfold G_B64; lia);
            rewrite (unsigned_lit_small (data + 3 * R + 1)) by lia;
            rewrite (unsigned_lit_small (data + 3 * R)) by lia;
            cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
            destruct (encR_dj_in_tab ltac:(lia)); destruct encR_dj_out_tab;
            repeat match goal with |- _ /\ _ => split end; try exact I;
            unfold G_B64 in *; lia)) as HS4.
    clear HS HSd. rename HS4 into HS.
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (U18l : U EE enc_Bx = SHADOW_OFF)
        by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
      assert (U11l : U EE (SOff 11 0) = q + 4 * R)
        by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | lia]);
      assert (U60l : U EE (SOff 60 0) = data + 3 * R)
        by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | lia]);
      assert (U70l : U EE (SOff 70 0) = data + 3 * R + 1)
        by (apply (U_atom _ 70%nat); [encT_peel 70%nat; apply ew_ewset_same | lia]);
      assert (U100l : U EE (SOff 100 0) = G_B64 + bA / 4)
        by (apply (U_atom _ 100%nat); [encT_peel 100%nat; apply ew_ewset_same
                                      | unfold G_B64; lia]);
      assert (U200l : U EE (SOff 200 0) = G_B64 + ((bA mod 4) * 16 + bB / 16))
        by (apply (U_atom _ 200%nat); [encT_peel 200%nat; apply ew_ewset_same
                                      | unfold G_B64; lia]);
      assert (E71l : ew EE 71 = w64 bB) by (encT_peel 71%nat; apply ew_ewset_same);
      assert (E11l : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
    end.
    assert (SHOK4 : sh_ok tfibsegs enc_Bx enc_tSHb2
      ltac:(lazymatch type of HS with st_ok _ ?EE _ _ => exact EE end)
      (mrestrict (w_H Wc) (ms_mem ms5))).
    { unfold enc_tSHb2, enc_tSHb1, enc_tSH2, enc_tSH1, enc_tSH. apply Forall_app. split.
      - apply Forall_app. split.
        + apply Forall_app. split.
          * apply Forall_app. split.
            -- constructor; [|constructor].
               exact (encT_sh_out (ms_mem ms5) _ _ (4 * R) HARU U18l U11l ltac:(lia) ltac:(lia)).
            -- constructor; [|constructor].
               exact (encT_sh_in (ms_mem ms5) _ _ 60%nat (data + 3 * R) (3 * R) HARU U18l U60l ltac:(lia) ltac:(lia) ltac:(lia)).
          * constructor; [|constructor].
            exact (encT_sh_in (ms_mem ms5) _ _ 70%nat (data + 3 * R + 1) (3 * R + 1) HARU U18l U70l ltac:(lia) ltac:(lia) ltac:(lia)).
        + constructor; [|constructor].
          exact (encR_shent_seat (ms_mem ms5) _ 100%nat (bA / 4) HA5 U18l U100l ltac:(lia)).
      - constructor; [|constructor].
        exact (encR_shent_seat (ms_mem ms5) _ 200%nat ((bA mod 4) * 16 + bB / 16) HA5 U18l U200l
          ltac:(lia)). }
    clear SHOK. rename SHOK4 into SHOK.
    (* 0x84a84 -> 0x84ac0: the store of c1 and the third index *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84ac0.
    all: first [ solve [ encT_awr E11l ] | idtac ].
    assert (HA6 : encR_agree (ms_mem ms6)) by (encT_agree HF5 HA5 E11l).
    assert (KEEP6 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms6)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP5 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr5
        ltac:(encT_wr E11l) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    (* drop the second table seat and seat 300 on g_b64 + the third index *)
    pose proof ((fun Hm => enc_drop_head _ _ _ _ _ Hm HS) ltac:(cbn [ss_mem]; reflexivity)) as HSd2.
    assert (RT2 : getr (ms_regs ms6) 12 = w64 (G_B64 + (bB mod 16) * 4)).
    { rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms6 12%bv HS).
      lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
      apply enc_denot_of_U. apply (enc_tU_addG _ _ ((bB mod 16) * 4));
        [ apply (enc_tU_i2 _ 71%nat bB); [encT_peel 71%nat; apply ew_ewset_same | lia] | lia ]. }
    pose proof (enc_seat_ro1 _ _ (restrict (w_H Wc) ms6) 12%bv 300 (G_B64 + (bB mod 16) * 4)
      (WriterSpec.b64c ((bB mod 16) * 4)) G_B64 (G_B64 + 63) HSd2
      ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) RT2
      ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(unfold G_B64; lia) ltac:(lia)
      ltac:(cbn [ms_mem restrict];
            exact (encR_tab_keep (ms_mem ms6) HA6 HTABc ((bB mod 16) * 4) ltac:(lia)))
      ltac:(apply all_disjoint_of_extents;
            unfold enc_tout, extent_of_region;
            cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val];
            encT_peel 300%nat; rewrite ew_ewset_same;
            encT_peel 70%nat; rewrite ew_ewset_same;
            encT_peel 60%nat; rewrite ew_ewset_same;
            encT_peel 11%nat; rewrite E11u;
            rewrite (unsigned_lit_small (G_B64 + (bB mod 16) * 4)) by (unfold G_B64; lia);
            rewrite (unsigned_lit_small (data + 3 * R + 1)) by lia;
            rewrite (unsigned_lit_small (data + 3 * R)) by lia;
            cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
            destruct (encR_dj_in_tab ltac:(lia)); destruct encR_dj_out_tab;
            repeat match goal with |- _ /\ _ => split end; try exact I;
            unfold G_B64 in *; lia)) as HS5.
    clear HS HSd2. rename HS5 into HS.
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (U18m : U EE enc_Bx = SHADOW_OFF)
        by (apply (U_atom _ 18%nat); [encT_peel 18%nat; exact A18 | unfold SHADOW_OFF; lia]);
      assert (U11m : U EE (SOff 11 0) = q + 4 * R)
        by (apply (U_atom _ 11%nat); [encT_peel 11%nat; exact A11 | lia]);
      assert (U60m : U EE (SOff 60 0) = data + 3 * R)
        by (apply (U_atom _ 60%nat); [encT_peel 60%nat; apply ew_ewset_same | lia]);
      assert (U70m : U EE (SOff 70 0) = data + 3 * R + 1)
        by (apply (U_atom _ 70%nat); [encT_peel 70%nat; apply ew_ewset_same | lia]);
      assert (U100m : U EE (SOff 100 0) = G_B64 + bA / 4)
        by (apply (U_atom _ 100%nat); [encT_peel 100%nat; apply ew_ewset_same
                                      | unfold G_B64; lia]);
      assert (U200m : U EE (SOff 200 0) = G_B64 + ((bA mod 4) * 16 + bB / 16))
        by (apply (U_atom _ 200%nat); [encT_peel 200%nat; apply ew_ewset_same
                                      | unfold G_B64; lia]);
      assert (U300m : U EE (SOff 300 0) = G_B64 + (bB mod 16) * 4)
        by (apply (U_atom _ 300%nat); [encT_peel 300%nat; apply ew_ewset_same
                                      | unfold G_B64; lia]);
      assert (E11m : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u)
    end.
    assert (SHOK5 : sh_ok tfibsegs enc_Bx enc_tSHb3
      ltac:(lazymatch type of HS with st_ok _ ?EE _ _ => exact EE end)
      (mrestrict (w_H Wc) (ms_mem ms6))).
    { unfold enc_tSHb3, enc_tSHb2, enc_tSHb1, enc_tSH2, enc_tSH1, enc_tSH.
      apply Forall_app. split.
      - apply Forall_app. split.
        + apply Forall_app. split.
          * apply Forall_app. split.
            -- apply Forall_app. split.
               ++ constructor; [|constructor].
                  exact (encT_sh_out (ms_mem ms6) _ _ (4 * R) HARU U18m U11m ltac:(lia) ltac:(lia)).
               ++ constructor; [|constructor].
                  exact (encT_sh_in (ms_mem ms6) _ _ 60%nat (data + 3 * R) (3 * R) HARU U18m U60m ltac:(lia) ltac:(lia)
                    ltac:(lia)).
            -- constructor; [|constructor].
               exact (encT_sh_in (ms_mem ms6) _ _ 70%nat (data + 3 * R + 1) (3 * R + 1) HARU U18m U70m ltac:(lia) ltac:(lia) ltac:(lia)).
          * constructor; [|constructor].
            exact (encR_shent_seat (ms_mem ms6) _ 100%nat (bA / 4) HA6 U18m U100m ltac:(lia)).
        + constructor; [|constructor].
          exact (encR_shent_seat (ms_mem ms6) _ 200%nat ((bA mod 4) * 16 + bB / 16) HA6 U18m U200m
            ltac:(lia)).
      - constructor; [|constructor].
        exact (encR_shent_seat (ms_mem ms6) _ 300%nat ((bB mod 16) * 4) HA6 U18m U300m ltac:(lia)). }
    clear SHOK. rename SHOK5 into SHOK.
    (* 0x84ac0 -> 0x84b24: the store of c2, the '=' and the fourth output byte *)
    fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84b24.
    all: first [ solve [ encT_awr E11m ] | idtac ].
    assert (HA7 : encR_agree (ms_mem ms7)) by (encT_agree HF6 HA6 E11m).
    assert (KEEP7 : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * R <= a < q + 4 * R + 4) ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms7)) a
      = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
    { intros a Ha Hx. rewrite <- (KEEP6 a Ha Hx). unfold mbyte.
      rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * R <= x < q + 4 * R + 4) HFr6
        ltac:(encT_wr E11m) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
      reflexivity. }
    (* the four bytes the tail stored *)
    pose proof (fsw_region_nth _ _ (restrict (w_H Wc) ms7) 3
      (YP09.mkRegion (Some 11%nat) 0 4 0 4
         [YP09.mkChunk 3 (CVal 1 (SLit 61)); YP09.mkChunk 2 (CVal 1 (SOff 301 0));
          YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))])
      HS ltac:(cbn [ss_mem nth_error]; reflexivity)) as HRout.
    cbn [ms_mem restrict] in HRout.
    lazymatch type of HS with st_ok _ ?EE _ _ =>
      assert (E11n : bv_unsigned (ew EE 11) = q + 4 * R) by (encT_peel 11%nat; exact E11u);
      assert (VQ : forall (od : Z) (e : sv) (v : Z),
        In (YP09.mkChunk od (CVal 1 e))
           [YP09.mkChunk 3 (CVal 1 (SLit 61)); YP09.mkChunk 2 (CVal 1 (SOff 301 0));
            YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))] ->
        sv_denot EE e = Z_to_bv 64 v -> 0 <= v < 256 ->
        val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms7)) (q + 4 * R + od) 1 v)
      by (intros od e v Hin Hd Hv;
          exact (fsw_field _ _ 11 (q + 4 * R) _ 0 4 0 4 od 1%N e v HRout E11n Hin Hd
            ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)))
    end.
    assert (VO0 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms7)) (q + 4 * R + 0) 1
      (WriterSpec.b64c (bA / 4)))
      by (apply (VQ 0 (SOff 101 0)); [cbn; tauto
          | rewrite fsw_SOff0; encT_peel 101%nat; apply ew_ewset_same | lia]).
    assert (VO1 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms7)) (q + 4 * R + 1) 1
      (WriterSpec.b64c ((bA mod 4) * 16 + bB / 16)))
      by (apply (VQ 1 (SOff 201 0)); [cbn; tauto
          | rewrite fsw_SOff0; encT_peel 201%nat; apply ew_ewset_same | lia]).
    assert (VO2 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms7)) (q + 4 * R + 2) 1
      (WriterSpec.b64c ((bB mod 16) * 4)))
      by (apply (VQ 2 (SOff 301 0)); [cbn; tauto
          | rewrite fsw_SOff0; encT_peel 301%nat; apply ew_ewset_same | lia]).
    assert (VO3 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms7)) (q + 4 * R + 3) 1 61)
      by (apply (VQ 3 (SLit 61)); [cbn; tauto
          | apply enc_denot_of_U; rewrite U_SLit; reflexivity | lia]).
    (* the model: two leftover bytes are encoded as three letters and one '=' *)
    assert (HLEN4 : Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs))) = 4 * R)
      by exact (encT_len4 R ltac:(lia) ltac:(lia)).
    assert (HMOD : WriterSpec.b64_enc bs
      = WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)
        ++ [WriterSpec.b64c (bA / 4); WriterSpec.b64c ((bA mod 4) * 16 + bB / 16);
            WriterSpec.b64c ((bB mod 16) * 4); 61]).
    { rewrite (enc_tsplit2 bs (Z.to_nat (3 * R)) (encT_split2_len R ltac:(lia) HL2)) at 1.
      rewrite (b64_enc_app (Z.to_nat R) _ _ (encT_firstn_len R ltac:(lia) ltac:(lia))).
      replace (S (Z.to_nat (3 * R))) with (Z.to_nat (3 * R + 1)) by lia.
      rewrite <- EbA, <- EbB. cbn [WriterSpec.b64_enc]. reflexivity. }
    assert (HPRE7 : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms7)) q (WriterSpec.b64_enc bs)).
    { rewrite HMOD. apply (encR_garr8_app4 _ _ _ _ _ _ q (4 * R));
        first [ solve [apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q _
                         (fun x => q + 4 * R <= x < q + 4 * R + 4) KEEP7 ltac:(lia)
                         ltac:(rewrite HLEN4; lia) ltac:(intros i Hi; rewrite HLEN4 in Hi; lia) HPRE)]
              | solve [exact HLEN4] | solve [lia] | solve [exact VO0] | solve [exact VO1]
              | solve [exact VO2] | solve [exact VO3] ]. }
    (* the hand-off at 0x84b24 *)
    apply (KNUL ms7 _);
      [ exact (encT_inv_mk (ms_mem ms7) _ HJ HARU HA7)
      | exact HPRE7
      | pose proof (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms7 HS
          ltac:(cbn [ss_resv]; reflexivity)) as HPC;
        lazymatch type of HPC with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
          let pc' := eval vm_compute in pc in change pc with pc' in HPC end;
        exact HPC
      | exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
                 ltac:(encT_peel 10%nat; rewrite A10; apply unsigned_lit_small; lia) ltac:(lia))
      | rewrite HQ3; replace (q + 4 * (R + 1)) with (q + 4 * R + 4) by lia;
        exact (enc_reg_val _ _ _ _ 11%bv 11 4 (q + 4 * R) HS ltac:(vm_compute; reflexivity)
                 ltac:(encT_peel 11%nat; exact E11u) ltac:(lia))
      | exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
                 ltac:(encT_peel 18%nat; rewrite A18; apply unsigned_lit_small;
                       unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))
      | unfold spZ; rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
          ltac:(vm_compute; reflexivity) ltac:(encT_peel 2%nat; rewrite A2; reflexivity)
          ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia));
        unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small;
          [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
           pose proof (u64_range (getr (ms_regs ms) 2)); lia]
      | apply encT_kept_mk; intros z Hz Hz2 Hz8 Hz9 Hz18 Hz19 Hz20;
        assert (HZ : z = 3 \/ z = 4 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26
                     \/ z = 27) by (unfold acallee_saved in Hz; lia);
        destruct HZ as [HE|[HE|[HE|[HE|[HE|[HE|[HE|[HE|HE]]]]]]]]; subst z;
        (lazymatch goal with |- getr (ms_regs ?mx) ?rx = _ =>
           rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ mx rx HS) end;
         lazymatch goal with |- sv_denot _ ?t = _ =>
           let t' := eval vm_compute in t in change t with t' end;
         rewrite fsw_SOff0;
         lazymatch goal with |- ew _ ?n = _ => encT_peel n end;
         lazymatch goal with |- ew _ ?n = getr _ ?r =>
           rewrite (ew_Ereg_nat (ms_regs ms) ([] : list word) n r
             ltac:(vm_compute; reflexivity)) end;
         apply (encT_kept_use ms Rk); solve [unfold acallee_saved; lia | lia]) ].
Qed.

(* encR_tail (A's name and binder order, lib/A/FSW_preset_base64_encode.v at a working branch
   6e3b1de9c97): the tail from 0x849bc, composed with encR_nul, so its post is encode_spec's *)
Lemma encR_tail : forall ms md R,
  encR_inv (ms_mem ms) md ->
  encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x849bc) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  0 <= R -> 3 * R < len < 3 * R + 3 ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md R H4 H5 H6 H7 H1 (H2 & H3).
apply (encT_tail_k ms md R _ H1 H2 ltac:(lia) H4 H5 H6 H7).
intros ms' md' K1 K2 K3 K4 K5 K6 K7 K8. exact (encR_nul ms' md' K1 K2 K3 K4 K5 K6 K7 K8).
Qed.

(* ---- the loop's exit 0x849b8 `bgeu a3,s0,84b24`: with len = 3R the walk is done and goes to the NUL store,
   otherwise the tail runs (0x849bc) ---- *)
Lemma encT_loop_exit_k : forall ms md R (Q : world tfibsegs -> config -> Prop),
  0 <= R -> 3 * R <= len -> len <= 3 * R + 2 ->
  encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x849b8) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  (forall ms' md',
     encR_inv (ms_mem ms') md' ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q (WriterSpec.b64_enc bs) ->
     ms' = mkst (ms_regs ms') (w64 0x84b24) (ms_mem ms') (seg_rom tfibsegs) ->
     getr (ms_regs ms') 10 = w64 q ->
     getr (ms_regs ms') 11 = w64 (q + 4 * ((len + 2) / 3)) ->
     getr (ms_regs ms') 18 = w64 SHADOW_OFF ->
     spZ (ms_regs ms') = spZ regs0 - 48 ->
     encR_kept ms' ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg ms md) Q.
Proof.
intros ms md R Q HR0 HRle HRle2 HINV HX Hms HPRE KNUL.
destruct (encT_inv_dest (ms_mem ms) md HINV) as (HJ & HARU & HA).
destruct (encT_exit_dest ms R HX) as (R8 & R9 & R10 & R11 & R13 & R14 & R18 & Rsp & Rk).
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
assert (HSZ : 4 * R + 1 <= enc_size len) by (unfold enc_size; Z.div_mod_to_equations; lia).
assert (HS : st_ok tfibsegs (Ereg (ms_regs ms) ([] : list word)) enc_exit_ss (restrict (w_H Wc) ms)).
{ rewrite Hms.
  apply (encT_exit_state Wc (ms_mem ms) (ms_regs ms) _ (q + 4 * R) (3 * R));
    first [ apply regs_ok_Ereg | exact R8 | exact R9 | exact R11 | exact R13 | exact R14 | exact R18
          | unfold PTOP in *; lia ]. }
assert (A8e : ew (Ereg (ms_regs ms) ([] : list word)) 8 = w64 len)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact R8).
assert (A9 : ew (Ereg (ms_regs ms) ([] : list word)) 9 = w64 data)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact R9).
assert (A10 : ew (Ereg (ms_regs ms) ([] : list word)) 10 = w64 q)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl); exact R10).
assert (A11 : ew (Ereg (ms_regs ms) ([] : list word)) 11 = w64 (q + 4 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact R11).
assert (A13 : ew (Ereg (ms_regs ms) ([] : list word)) 13 = w64 (3 * R))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 13 13%bv eq_refl); exact R13).
assert (A18 : ew (Ereg (ms_regs ms) ([] : list word)) 18 = w64 SHADOW_OFF)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact R18).
assert (A2 : ew (Ereg (ms_regs ms) ([] : list word)) 2 = getr (ms_regs ms) 2)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); reflexivity).
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (U13x : U EE (SOff 13 0) = 3 * R)
    by (apply (U_atom _ 13%nat); [exact A13 | lia]);
  assert (U8x : U EE (SOff 8 0) = len)
    by (apply (U_atom _ 8%nat); [exact A8e | lia])
end.
eapply SRr_sym_branch with (c := BC_GEU) (a := SOff 13 0) (b := SOff 8 0);
  [exact HS | intros Hbr HSb | intros Hbr HSb];
  rewrite branch_geu_U, U13x, U8x in Hbr;
  [apply negb_true_iff, Z.ltb_ge in Hbr | apply negb_false_iff, Z.ltb_lt in Hbr].
- (* 3R >= len, so len = 3R: the walk is done, the run goes to the NUL store *)
  assert (HL0 : len = 3 * R) by lia.
  clear HS. rename HSb into HS.
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU 0x84b24.
  all: first [ solve [cbn [enc_exit_ss add_cond ss_mem]; apply awr_ok_nil] | idtac ].
  assert (HKP : forall a, 0 <= a < 2 ^ 64 ->
    mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a
    = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
  { intros a Ha. unfold mbyte.
    rewrite (enc_frame_X _ _ _ _ (fun _ : Z => False) HFr
      ltac:(intros z (rg & Hrin & _); cbn [enc_exit_ss add_cond ss_mem] in Hrin; destruct Hrin)
      (Z_to_bv 64 a) ltac:(intros HFz; destruct HFz)).
    reflexivity. }
  apply (KNUL ms0 _);
    [ apply (encT_inv_mk (ms_mem ms0) _ HJ HARU);
      intros x Hx; rewrite (enc_frame_X _ _ _ _ encR_out HF
        ltac:(intros z (rg & Hrin & _); cbn [enc_exit_ss add_cond ss_mem] in Hrin; destruct Hrin)
        x Hx); exact (HA x Hx)
    | rewrite firstn_all2 in HPRE by lia;
      apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q (WriterSpec.b64_enc bs) (fun _ : Z => False)
        ltac:(intros a Ha _; exact (HKP a Ha)) ltac:(lia)
        ltac:(pose proof encT_len_all; lia)
        ltac:(intros i Hi HFz; destruct HFz) HPRE)
    | pose proof (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms0 HS
        ltac:(cbn [ss_resv]; reflexivity)) as HPC;
      lazymatch type of HPC with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
        let pc' := eval vm_compute in pc in change pc with pc' in HPC end;
      exact HPC
    | exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
               ltac:(encT_peel 10%nat; rewrite A10; apply unsigned_lit_small; lia) ltac:(lia))
    | replace (q + 4 * ((len + 2) / 3)) with (q + 4 * R)
        by (rewrite HL0; replace (3 * R + 2) with (R * 3 + 2) by lia;
            rewrite Z.div_add_l by lia; cbn; lia);
      exact (enc_reg_val0 _ _ _ _ 11%bv 11 (q + 4 * R) HS ltac:(vm_compute; reflexivity)
               ltac:(encT_peel 11%nat; rewrite A11; apply unsigned_lit_small; lia) ltac:(lia))
    | exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
               ltac:(encT_peel 18%nat; rewrite A18; apply unsigned_lit_small;
                     unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia))
    | unfold spZ; rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
        ltac:(vm_compute; reflexivity) ltac:(encT_peel 2%nat; rewrite A2; reflexivity)
        ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia));
      unfold w64; rewrite Z_to_bv_unsigned, bv_wrap_small;
        [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
         pose proof (u64_range (getr (ms_regs ms) 2)); lia]
    | apply encT_kept_mk; intros z Hz Hz2 Hz8 Hz9 Hz18 Hz19 Hz20;
      assert (HZ : z = 3 \/ z = 4 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26
                   \/ z = 27) by (unfold acallee_saved in Hz; lia);
      destruct HZ as [HE|[HE|[HE|[HE|[HE|[HE|[HE|[HE|HE]]]]]]]]; subst z;
      (lazymatch goal with |- getr (ms_regs ?mx) ?rx = _ =>
         rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ mx rx HS) end;
       lazymatch goal with |- sv_denot _ ?t = _ =>
         let t' := eval vm_compute in t in change t with t' end;
       rewrite fsw_SOff0;
       lazymatch goal with |- ew _ ?n = _ => encT_peel n end;
       lazymatch goal with |- ew _ ?n = getr _ ?r =>
         rewrite (ew_Ereg_nat (ms_regs ms) ([] : list word) n r
           ltac:(vm_compute; reflexivity)) end;
       apply (encT_kept_use ms Rk); solve [unfold acallee_saved; lia | lia]) ].
- (* 3R < len: the tail runs *)
  clear HS. rename HSb into HS.
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU 0x849bc.
  all: first [ solve [cbn [enc_exit_ss add_cond ss_mem]; apply awr_ok_nil] | idtac ].
  assert (HKP : forall a, 0 <= a < 2 ^ 64 ->
    mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms0)) a
    = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
  { intros a Ha. unfold mbyte.
    rewrite (enc_frame_X _ _ _ _ (fun _ : Z => False) HFr
      ltac:(intros z (rg & Hrin & _); cbn [enc_exit_ss add_cond ss_mem] in Hrin; destruct Hrin)
      (Z_to_bv 64 a) ltac:(intros HFz; destruct HFz)).
    reflexivity. }
  apply (encT_tail_k ms0 _ R Q HR0 ltac:(lia) HRle2);
    [ apply (encT_inv_mk (ms_mem ms0) _ HJ HARU);
      intros x Hx; rewrite (enc_frame_X _ _ _ _ encR_out HF
        ltac:(intros z (rg & Hrin & _); cbn [enc_exit_ss add_cond ss_mem] in Hrin; destruct Hrin)
        x Hx); exact (HA x Hx)
    | split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]]
    | pose proof (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms0 HS
        ltac:(cbn [ss_resv]; reflexivity)) as HPC;
      lazymatch type of HPC with _ = mkst _ (Z_to_bv 64 ?pc) _ _ =>
        let pc' := eval vm_compute in pc in change pc with pc' in HPC end;
      exact HPC
    | apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q
        (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) (fun _ : Z => False)
        ltac:(intros a Ha _; exact (HKP a Ha)) ltac:(lia)
        ltac:(pose proof (encT_len4 R HR0 HRle) as HL4; lia)
        ltac:(intros i Hi HFz; destruct HFz) HPRE)
    | exact KNUL ].
  + exact (enc_reg_val0 _ _ _ _ 8%bv 8 len HS ltac:(vm_compute; reflexivity)
             ltac:(encT_peel 8%nat; rewrite A8e; apply unsigned_lit_small; lia) ltac:(lia)).
  + exact (enc_reg_val0 _ _ _ _ 9%bv 9 data HS ltac:(vm_compute; reflexivity)
             ltac:(encT_peel 9%nat; rewrite A9; apply unsigned_lit_small; lia) ltac:(lia)).
  + exact (enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
             ltac:(encT_peel 10%nat; rewrite A10; apply unsigned_lit_small; lia) ltac:(lia)).
  + exact (enc_reg_val0 _ _ _ _ 11%bv 11 (q + 4 * R) HS ltac:(vm_compute; reflexivity)
             ltac:(encT_peel 11%nat; rewrite A11; apply unsigned_lit_small; lia) ltac:(lia)).
  + exact (enc_reg_val0 _ _ _ _ 13%bv 13 (3 * R) HS ltac:(vm_compute; reflexivity)
             ltac:(encT_peel 13%nat; rewrite A13; apply unsigned_lit_small; lia) ltac:(lia)).
  + rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 14%bv HS).
    lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
    reflexivity.
  + exact (enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
             ltac:(encT_peel 18%nat; rewrite A18; apply unsigned_lit_small;
                   unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
  + unfold spZ. rewrite (enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
      ltac:(vm_compute; reflexivity) ltac:(encT_peel 2%nat; rewrite A2; reflexivity)
      ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia)).
    unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small;
      [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
       pose proof (u64_range (getr (ms_regs ms) 2)); lia].
  + apply encT_kept_mk. intros z Hz Hz2 Hz8 Hz9 Hz18 Hz19 Hz20.
    assert (HZ : z = 3 \/ z = 4 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26
                 \/ z = 27) by (unfold acallee_saved in Hz; lia).
    destruct HZ as [HE|[HE|[HE|[HE|[HE|[HE|[HE|[HE|HE]]]]]]]]; subst z;
    (lazymatch goal with |- getr (ms_regs ?mx) ?rx = _ =>
       rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ mx rx HS) end;
     lazymatch goal with |- sv_denot _ ?t = _ =>
       let t' := eval vm_compute in t in change t with t' end;
     rewrite fsw_SOff0;
     lazymatch goal with |- ew _ ?n = _ => encT_peel n end;
     lazymatch goal with |- ew _ ?n = getr _ ?r =>
       rewrite (ew_Ereg_nat (ms_regs ms) ([] : list word) n r
         ltac:(vm_compute; reflexivity)) end;
     apply (encT_kept_use ms Rk); solve [unfold acallee_saved; lia | lia]).
Qed.

(* encR_loop_exit (A's name and binder order = encR_loop's KEXIT, lib/A/FSW_preset_base64_encode.v at
   a working branch 0a3016aa4bf): the exit 0x849b8 composed with the tail and encR_nul *)
Lemma encR_loop_exit : forall ms md R,
  len <= 3 * R + 2 -> 3 * R <= len ->
  encR_inv (ms_mem ms) md -> encR_exit_regs ms R ->
  ms = mkst (ms_regs ms) (w64 0x849b8) (ms_mem ms) (seg_rom tfibsegs) ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
  SRr tfibsegs Wc (mkCfg ms md)
    (fpostU tfibsegs B STK_preset_base64_encode (spZ regs0) FS_PSTAT_FP regs0 ly0 St0 U0 W0 mem0 md0
       EV_preset_base64_encode (U0 ++ [(q - HEAD, HEAD)]) encR_Q).
Proof.
intros ms md R H3 H2 H4 H5 H6 H7.
apply (encT_loop_exit_k ms md R _ ltac:(lia) H2 H3 H4 H5 H6 H7).
intros ms' md' K1 K2 K3 K4 K5 K6 K7 K8. exact (encR_nul ms' md' K1 K2 K3 K4 K5 K6 K7 K8).
Qed.

End R.

End W.
