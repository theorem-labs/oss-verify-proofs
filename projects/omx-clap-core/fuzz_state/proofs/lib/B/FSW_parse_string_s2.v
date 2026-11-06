(* fs program part, READER group, image B (fs.asan-ubsan): the ASan walk of parse_string (A_parse_string 0x85534,
   pf.c:117-181), PLAIN-BYTE CASE, STAGE 2: the return of fuzz_malloc 0x85618 -> `ret` 0x85a5c.
   rule 24: proves function parse_string, image B (this file: stage 2 of the walk; stage 1, the fuzz_malloc call step
   and the composition parse_string_proof_c5 are lib/B/FSW_parse_string.v, which Requires this file). Reuse search
   (a Theorem Labs lane 2026-10-29T04:09Z, proof-index v5 built 04:08:23Z, a Theorem Labs lane's idx-B-parse_string.txt; by address B
   0x85534, no trampoline; named cold branches and all 10067 cold refs, a Theorem Labs lane reuse-parse_string.md:13-33;
   CONFIRM 2026-10-29T04:34Z, a Theorem Labs lane: the search holds): the only lib/B proof of parse_string
   is the bespoke line a working branch 955803f9b2e lib/B/Prog/parse_string*.v, stated over another
   engine, so it is a template here, not a port source.

   TEMPLATES.
   - the image-A walk, PROVED: a working branch 9f3343583b7 lib/A/FSW_parse_string.v, Section W2
     (:1049-1997: ps2_* helpers, the copy loop's states, ps2_step / ps2_post / ps2_exit / ps2_loop / ps2_r0,
     ps2_blocks, pstr_stage2). Its structure, definitions and lemma names are ported; the addresses, the register
     allocation and the block layout are B's.
   - the bespoke image-B proof (cut points and registers only, not imported): a working branch 955803f9b2e
     lib/B/Prog/parse_string_segs.v:211-229 (aps_alloc_setup: the registers at 0x85618 and the loop head 0x85678),
     lib/B/Prog/parse_string.v:1180 (aps_some, the Some-Q path), parse_string_segs.v:55-61 (aps_ck_out, the exit at
     0x85a60).

   B's CODE on this path: at the return 0x85618 a0 = a (the new block), s0 = q,
   s1 = q + 8, s4 = p + 1 (the read cursor), s6 = shadow cell of q, s7 = the shadow base, s8 = shadow cell of q + 8
   (A: s7 / s8 / s9). 0x85618 `beqz a0` (not taken), s2 := a, the 8-byte shadow check of in->end (0x85620 through s8),
   in->end into a0, 0x8562c `bgeu s4, a0` (not taken: p + 1 < text + len), the constants (s9 = 0x22, a4 = 0x20,
   s11 = 0x5c, s10 = -1, a5..t0) and the three hex4 words at sp + 8 .. sp + 0x20, s3 := s2; the copy loop head 0x85678:
   the shadow check of the byte at s4, 0x8568c `beq a2, s9` (the closing quote: exit), the shadow check again,
   0x8569c `bltu a1, a4` (not taken: plain bytes are >= 0x20), 0x856a4 `bne a1, s11` (taken: no backslash) to 0x85730,
   the UBSan tests `beq s4, s10` / `beq s3, s10` (not taken), the shadow check of the store at s3, `sb a1, 0(s3)`,
   s3 += 1, the shadow check of in->end and its reload into a0, s4 := s5 = s4 + 1, 0x85764 `bltu s5, a0` (taken: the
   loop goes on). The exit 0x85a60: the shadow check of the NUL's byte at s3, `sb zero, 0(s3)` 0x85a74, `beq s4, -1`
   (not taken), the 8-byte shadow check of in->p (through s6), in->p := s4 + 1 (`sd` 0x85a88), a0 := s2, the epilogue
   0x85a24..0x85a58 and the `ret` 0x85a5c. No __asan_report_* branch is taken and the UBSan trap 0x85a90 is not reached.
   MEASURED on the engine (sym_runN_tok / sym_run_toN_tok over parse_string_tbl, a Theorem Labs lane's M1.v .. M3.v):
   r0 stops at 0x8562c (one 8-byte obligation at s1), then runs to 0x85678; one loop turn stops at 0x8568c, 0x856a4
   and 0x85764 (obligations: the text byte twice, in->end) and runs back to 0x85678; the exit is one run
   0x85678 -> 0x85a5c (obligations: in->p, the text byte).

   The shared definitions (RA_PSTR_MALLOC, FRAME_PSTR, pstr_saved, pstr_frame_at, pstr_ret_facts, the range_addressable
   readers pstr_RA_stk_mem / pstr_RA_blk_mem, pstr_val_mem_eq_at, ps2_req, ps2_img_hi) are
   lib/B/FSW_parse_string_defs.v (675315ade48). No Admitted, no Axiom, no Parameter, no admit, no timeout. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSW_K FSW_ret FSW_parse_string_tbl.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSPstat FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import FSupoisonStack FSW_parse_string_defs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjIn PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib Require KindBGlue.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= stage 2: the return of fuzz_malloc 0x85618 -> `ret` 0x85a5c =================
   The copy loop 0x85678..0x85764, the NUL 0x85a74, the in->p store 0x85a88, the epilogue 0x85a20..0x85a58 and the
   return itself (FSW_ret.v fsw_retU), concluding parse_string_spec's fpostU. Its premises are the spec's plus
   pstr_ret_facts: what the fuzz_malloc call step hands back. *)
Section W2. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis TL_got : as_got_shadow B = tfib_D_GOT_asan_shadow_memory_dynamic_address.
Hypothesis TL_cell : as_shadow_cell B = tfib_D_asan_shadow_memory_dynamic_address.

(* ---- the walk's symbolic vocabulary: inside the body the shadow base is s7 (atom 23), and s6 / s8 hold the shadow
   cells of in->p / in->end as `(x >> 3) + s7`, the form the token engine reads (YCbn.v match_x) ---- *)
Definition ps2_Bq : sv := SOff 23 0.
Definition ps2_shx (n : nat) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff 23 0).

(* ---- small helpers over the symbolic state and the machine's memory ---- *)
Lemma ps2_ewR : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r ->
  YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew (Ereg regs extra) n) = v.
Proof.
intros regs extra n r v Hn Hr Hv. rewrite (ew_Ereg_nat regs extra n r Hn), Hr. unfold w64. apply unsigned_lit_small; exact Hv.
Qed.
Lemma ps2_shx_denot : forall E n x, bv_unsigned (ew E n) = x -> bv_unsigned (ew E 23) = SHADOW_OFF ->
  0 <= x < 2 ^ 64 -> sv_denot E (ps2_shx n) = w64 (SHADOW_OFF + x / 8).
Proof.
intros E n x Hn H23 Hx. unfold ps2_shx, w64. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, U_SLit, Hn, H23, !Z.add_0_r.
replace (Z.land (zcanon 3) 63) with 3 by reflexivity. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
assert (Hd : 0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (zcanon_id x) by (unfold M64; lia). rewrite (zcanon_id (x / 8)) by (unfold M64; lia).
rewrite (zcanon_id SHADOW_OFF) by (unfold M64, SHADOW_OFF; lia). rewrite Z.add_comm. apply zcanon_id.
unfold M64, SHADOW_OFF. lia.
Qed.
Lemma ps2_reg_val : forall (H : word -> bool) E ss ms (r : bv 5) e v,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot E e = w64 v ->
  YK11.getr (ms_regs ms) r = w64 v.
Proof. intros H E ss ms r e v HS Hr He. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr. exact He. Qed.
Lemma ps2_denot_off : forall E n z v w, bv_unsigned (ew E n) = v -> w = v + z -> 0 <= w < 2 ^ 64 ->
  sv_denot E (SOff n z) = w64 w.
Proof.
intros E n z v w Hn Hw Hz. subst w. unfold w64. apply bv_eq. rewrite denot_SOff, Hn, unsigned_lit_small by exact Hz.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma ps2_denot_lit : forall E z, 0 <= z < 2 ^ 64 -> sv_denot E (SLit z) = w64 z.
Proof.
intros E z Hz. unfold w64. apply bv_eq. change (bv_unsigned (sv_denot E (SLit z))) with (U E (SLit z)).
rewrite U_lit by exact Hz. rewrite unsigned_lit_small by exact Hz. reflexivity.
Qed.
Lemma ps2_U_off : forall E n z v, bv_unsigned (ew E n) = v -> 0 <= v + z < 2 ^ 64 -> U E (SOff n z) = v + z.
Proof. intros E n z v Hn Hz. rewrite U_SOff, Hn. apply zcanon_id. unfold M64. lia. Qed.
(* memory outside a run's write windows is the memory before it *)
Definition ps2_wins_b (ws : list (nat * Z * Z)) (r : YP09.region) : bool :=
  (YP09.r_whi r <=? YP09.r_wlo r) ||
  existsb (fun w => obase_eqb (YP09.r_base r) (Some (fst (fst w))) && (YP09.r_wlo r =? snd (fst w)) &&
                    (YP09.r_whi r =? snd w)) ws.
Lemma ps2_frame_wins : forall E rs m m' (ws : list (nat * Z * Z)),
  forallb (ps2_wins_b ws) rs = true -> frame_of E rs m m' ->
  forall x : word, Forall (fun w => ~ (bv_unsigned (ew E (fst (fst w))) + snd (fst w) <= bv_unsigned x <
                                       bv_unsigned (ew E (fst (fst w))) + snd w)) ws -> m' x = m x.
Proof.
intros E rs m m' ws Hb HF x Hx. apply HF. intros (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hc. unfold ps2_wins_b in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
apply existsb_exists in Hc as (w & Hw & Hc).
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hbase Hlo]. apply Z.eqb_eq in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hx w Hw) as Hn. cbv beta in Hn.
destruct (YP09.r_base r) as [k|]; [|discriminate]. cbn [obase_eqb] in Hbase. apply Nat.eqb_eq in Hbase. subst k.
cbn [base_val] in Ha. apply Hn. lia.
Qed.
Lemma ps2_mbyte_eq : forall (H : word -> bool) m m' x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  mbyte tfibsegs (mrestrict H m') x = mbyte tfibsegs (mrestrict H m) x.
Proof. intros H m m' x E. unfold mbyte, mrestrict. rewrite E. reflexivity. Qed.
Lemma ps2_wr_eq : forall (H : word -> bool) m m' x, m' (Z_to_bv 64 x) = m (Z_to_bv 64 x) ->
  (writable_at tfibsegs (mrestrict H m) x <-> writable_at tfibsegs (mrestrict H m') x).
Proof. intros H m m' x E. unfold writable_at, wview, mrestrict. rewrite E. reflexivity. Qed.
Lemma ps2_bytes_at_eq : forall (H : word -> bool) m m' a bs,
  (forall k, (k < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  lib.Lib.Mem.bytes_at tfibsegs (mrestrict H m) a bs -> lib.Lib.Mem.bytes_at tfibsegs (mrestrict H m') a bs.
Proof.
intros H m m' a bs E (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|]. intros k Hk.
rewrite <- (H2 k Hk). unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa, mrestrict. rewrite (E k Hk). reflexivity.
Qed.
(* one byte of a region's 1-byte chunk *)
Lemma ps2_chunk1 : forall E m n lo hi wlo whi cs off v,
  region_ok tfibsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> In (YP09.mkChunk off (CVal 1 v)) cs ->
  mbyte tfibsegs m (bv_unsigned (ew E n) + off) = Some (Z_to_bv 8 (bv_unsigned (sv_denot E v))).
Proof.
intros E m n lo hi wlo whi cs off v (_ & _ & _ & Hcs) Hc.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (b & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off] in Hb1, Hb2.
rewrite Z.add_0_r in Hb2. rewrite Hb2. injection Hb1 as <-. unfold byte_of_word. rewrite Z.mul_0_r, Z.shiftr_0_r.
reflexivity.
Qed.
Lemma ps2_nz : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H Hc. subst r. apply H. reflexivity. Qed.
Lemma ps2_chunk1_ok : forall E m base off e (c : byte), sv_denot E e = w64 (bv_unsigned c) ->
  mbyte tfibsegs m (base + off) = Some c -> YP09.chunk_ok tfibsegs E m base (YP09.mkChunk off (CVal 1 e)).
Proof.
intros E m base off e c He Hm i Hi. cbn [YP09.c_len YP09.c_val cv_len] in Hi.
assert (i = 0) by (change (Z.of_N 1) with 1 in Hi; lia). subst i. exists c. cbn [cbyte YP09.c_val YP09.c_off].
rewrite He. unfold byte_of_word, w64. rewrite Z.mul_0_r, Z.shiftr_0_r.
pose proof (YK11.u8_range c). rewrite unsigned_lit_small by lia. rewrite Z_to_bv_bv_unsigned.
split; [reflexivity|]. rewrite Z.add_0_r. exact Hm.
Qed.
(* a run's memory chain: every byte but the one window [v, v + 1) is the memory before the run *)
Lemma ps2_chain1 : forall E rs (m m' m0 : word -> option byte) (n : nat) v,
  frame_of E rs m m' -> forallb (ps2_wins_b [(n, 0, 1)]) rs = true -> bv_unsigned (ew E n) = v ->
  (forall x : word, bv_unsigned x <> v -> m x = m0 x) -> forall x : word, bv_unsigned x <> v -> m' x = m0 x.
Proof.
intros E rs m m' m0 n v HF Hb Hn HM x Hx. rewrite <- (HM x Hx).
apply (ps2_frame_wins E rs m m' [(n, 0, 1)] Hb HF x). constructor; [|constructor]. cbn [fst snd]. lia.
Qed.
Lemma ps2_awr_wins : forall E rs ws STK sp0 FP bl0 blc lyc own fr0,
  forallb (ps2_wins_b ws) rs = true ->
  Forall (fun w => forall x, bv_unsigned (ew E (fst (fst w))) + snd (fst w) <= x <
    bv_unsigned (ew E (fst (fst w))) + snd w -> awr_byte tfibsegs B STK sp0 FP bl0 blc lyc own fr0 x) ws ->
  awr_ok tfibsegs B E rs STK sp0 FP bl0 blc lyc own fr0.
Proof.
intros E rs ws STK sp0 FP bl0 blc lyc own fr0 Hb Hw x (r & Hr & Ha).
pose proof (proj1 (forallb_forall _ _) Hb r Hr) as Hc. unfold ps2_wins_b in Hc.
apply orb_prop in Hc as [Hc|Hc]; [apply Z.leb_le in Hc; lia|].
apply existsb_exists in Hc as (w & Hwin & Hc).
apply andb_prop in Hc as [Hc Hhi]. apply andb_prop in Hc as [Hbase Hlo]. apply Z.eqb_eq in Hlo, Hhi.
pose proof (proj1 (Forall_forall _ _) Hw w Hwin) as Hx. cbv beta in Hx.
destruct (YP09.r_base r) as [k|]; [|discriminate]. cbn [obase_eqb] in Hbase. apply Nat.eqb_eq in Hbase. subst k.
cbn [base_val] in Ha. apply Hx. lia.
Qed.
(* the frame words of the 13 saved registers lie in [sp + 0x28, sp + 0x90) *)
Lemma ps2_frame_keep : forall (W : world tfibsegs) m m' regs0 sp,
  0 <= sp -> sp + 144 <= 2 ^ 64 ->
  (forall y, sp + 40 <= y < sp + 144 -> m' (Z_to_bv 64 y) = m (Z_to_bv 64 y)) ->
  pstr_frame_at W m regs0 sp -> pstr_frame_at W m' regs0 sp.
Proof.
intros W m m' regs0 sp H0 H1 HM HF. unfold pstr_frame_at in *.
assert (Hb : Forall (fun c => 40 <= fst c /\ fst c + 8 <= 144) pstr_saved)
  by (unfold pstr_saved; repeat constructor; cbn [fst]; lia).
rewrite Forall_forall in HF, Hb |- *. intros c Hc. apply (pstr_val_mem_eq_at _ m m'); [|exact (HF c Hc)].
intros k Hk. pose proof (Hb c Hc). apply HM. lia.
Qed.

(* ---- the copy loop's symbolic states (measured on the engine, see the header) ---- *)
(* the loop head 0x85678: the byte at the read cursor s4 (atom 20) is extra atom 32, the write cursor is s3 (atom 19),
   in->end at s1 is extra atom 33; the constants s9 = 0x22, a4 = 0x20, s11 = 0x5c, s10 = -1 and the shadow cells s6 / s8 *)
Definition ps2_srL : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms 25%bv (SLit 34)) 14%bv (SLit 32)) 27%bv (SLit 92)) 26%bv
    (SLit 18446744073709551615)) 24%bv (ps2_shx 9)) 22%bv (ps2_shx 8).
Definition ps2_rgL : list YP09.region :=
  [YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))];
   YP09.mkRegion (Some 19%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))]].
Definition ps2_faL : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3);
   (19%nat, mkAF 4096 0x7fffff800000 0); (20%nat, mkAF 4096 0x7fffff800000 0);
   (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 32 255 0); (33%nat, mkAF 0 (2 ^ 62) 0)] [] [].
Definition ps2_SHL : list shent := [mkSHE 19 0 1].
Definition ps2_ssL : sstate := mkSS 0x85678 ps2_srL ps2_rgL None ps2_faL.
(* the state at the return of fuzz_malloc 0x85618: the frame slots 8..0x20 (written) and in->end at s1 *)
Definition ps2_sr0 : list sv := sr_set sr_atoms 24%bv (ps2_shx 9).
Definition ps2_rg0 : list YP09.region :=
  [YP09.mkRegion (Some 2%nat) 8 32 8 32 [];
   YP09.mkRegion (Some 9%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))]].
Definition ps2_fa0 : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 16) 3); (10%nat, mkAF 4112 0x7fffff800000 4);
   (20%nat, mkAF 4096 0x7fffff800000 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 62) 0)] [] [].
Definition ps2_ss0 : sstate := mkSS 0x85618 ps2_sr0 ps2_rg0 None ps2_fa0.
Lemma ps2_chainw : forall E rs (m m' m0 : word -> option byte) (n : nat) lo hi v,
  frame_of E rs m m' -> forallb (ps2_wins_b [(n, lo, hi)]) rs = true -> bv_unsigned (ew E n) = v ->
  (forall x : word, ~ (v + lo <= bv_unsigned x < v + hi) -> m x = m0 x) ->
  forall x : word, ~ (v + lo <= bv_unsigned x < v + hi) -> m' x = m0 x.
Proof.
intros E rs m m' m0 n lo hi v HF Hb Hn HM x Hx. rewrite <- (HM x Hx).
apply (ps2_frame_wins E rs m m' [(n, lo, hi)] Hb HF x). constructor; [|constructor]. cbn [fst snd]. lia.
Qed.

(* the exit state at the loop head when the byte is the closing quote: the quote at s4, the NUL's byte at s3, in->p at
   s0 (written), and the 13 frame words the epilogue reloads (extra atoms 32 .. 44, pstr_saved's order) *)
Definition ps2_fchunks : list YP09.chunk :=
  [YP09.mkChunk 0x88 (CVal 8 (SOff 32 0)); YP09.mkChunk 0x80 (CVal 8 (SOff 33 0));
   YP09.mkChunk 0x78 (CVal 8 (SOff 34 0)); YP09.mkChunk 0x70 (CVal 8 (SOff 35 0));
   YP09.mkChunk 0x68 (CVal 8 (SOff 36 0)); YP09.mkChunk 0x60 (CVal 8 (SOff 37 0));
   YP09.mkChunk 0x58 (CVal 8 (SOff 38 0)); YP09.mkChunk 0x50 (CVal 8 (SOff 39 0));
   YP09.mkChunk 0x48 (CVal 8 (SOff 40 0)); YP09.mkChunk 0x40 (CVal 8 (SOff 41 0));
   YP09.mkChunk 0x38 (CVal 8 (SOff 42 0)); YP09.mkChunk 0x30 (CVal 8 (SOff 43 0));
   YP09.mkChunk 0x28 (CVal 8 (SOff 44 0))].
Definition ps2_rgX : list YP09.region :=
  [YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 34))];
   YP09.mkRegion (Some 19%nat) 0 1 0 1 [];
   YP09.mkRegion (Some 8%nat) 0 8 0 8 [];
   YP09.mkRegion (Some 2%nat) 40 144 0 0 ps2_fchunks].
Definition ps2_faX : facts := mkFacts
  [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (8%nat, mkAF (2 ^ 46) (2 ^ 47 - 24) 3);
   (19%nat, mkAF 4096 0x7fffff800000 0); (20%nat, mkAF 4096 0x7fffff800000 0);
   (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition ps2_ssX : sstate := mkSS 0x85678 ps2_srL ps2_rgX None ps2_faX.
Definition ps2_xsX (regs0 : bvmap 5 word) : list word := map (fun c => YK11.getr regs0 (Z_to_bv 5 (snd c))) pstr_saved.
(* what the run leaves in each callee-saved register at the `ret` *)
Definition ps2_expect (r : bv 5) : sv :=
  let z := bv_unsigned r in
  if z =? 2 then SOff 2 144 else if z =? 3 then SOff 3 0 else if z =? 4 then SOff 4 0
  else if z =? 8 then SOff 33 0 else if z =? 9 then SOff 34 0 else SOff (Z.to_nat (z + 17)) 0.
Lemma ps2_fchunk : forall E m sp off (n : nat) v, val_mem tfibsegs m (sp + off) 8 v ->
  sv_denot E (SOff n 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  YP09.chunk_ok tfibsegs E m sp (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros E m sp off n v Hv He Hr. apply (chunk_ok_val tfibsegs E m sp off 8 (SOff n 0) v He); [cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
exact Hv.
Qed.

Section L.
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ot q text len p d : Z) (tb : list byte) (tcap Q live peak cnt fail a : Z)
  (ly2 : alayout) (S2 : astate) (W2 : world tfibsegs) (mem2 : word -> option byte).
Hypothesis Hra : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis HSPal : spZ regs mod 16 = 0.
Hypothesis Hceil : alloc_ceiling <= ly_stk_lo ly.
Hypothesis HSTK : ly_stk_lo ly + STK_parse_string <= spZ regs.
Hypothesis Hot : ot <= ly_stk_hi ly.
Hypothesis H47 : ly_stk_hi ly <= 2 ^ 47.
Hypothesis Hq1 : spZ regs <= q.
Hypothesis Hq2 : q + 24 <= ot.
Hypothesis Hlo2 : ly_stk_lo ly2 = ly_stk_lo ly.
Hypothesis Hhi2 : ly_stk_hi ly2 = ly_stk_hi ly.
Hypothesis HIN2 : PjIn.pj_in_ok tfibsegs (mrestrict (w_H W2) mem2) q text len p d tb.
Hypothesis HTX2 : rd_text tfibsegs B ly2 S2 W2 mem2 text len tcap.
Hypothesis HTX1 : In (text - HEAD, tcap + HEAD) (ablocks B ly S).
Hypothesis Hrun : plain_run tb text len p Q.
Hypothesis Hab : ablocks B ly2 S2 = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)].
Hypothesis Ha16 : 4096 + HEAD <= a.
Hypothesis Ham : a mod 16 = 0.
Hypothesis HRB : fs_rblock tfibsegs B ly2 S2 W2 mem2 a (Q + 1).
Hypothesis HFH : FSupoisonU.fs_heads B ly2 S2 (U ++ [(a - HEAD, HEAD)]).
Hypothesis HWK : wkeep tfibsegs W W2 mem mem2 (spZ regs) ot q 24.
Hypothesis HGL : fs_glob tfibsegs W2 mem2 (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail.
(* the new block against the old ones (from AR at the return, ps2_blocks below) *)
Hypothesis Hnew : ~ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly S).
Hypothesis Hdisj : text + tcap <= a - HEAD \/ a + Q + 1 <= text - HEAD.
Hypothesis Hceil_a : a + Q + 1 <= alloc_ceiling.
Hypothesis Hceil_t : text + tcap <= alloc_ceiling.
Hypothesis Happ : a + Q + 1 <= kLowShadowBeg \/ kHighMemBeg <= a - HEAD.
Hypothesis Himg : forall x, a - HEAD <= x < a + Q + 1 -> ~ in_img tfibsegs x.

Definition ps2_U2 : list (Z * Z) := U ++ [(a - HEAD, HEAD)].
Definition ps2_STKw : Z := STK_parse_string + (ot - spZ regs).
Definition ps2_PQ : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    YK11.getr regs' 10 = w64 a /\ 4096 + HEAD <= a /\
    ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] /\
    fs_rblock tfibsegs B ly' S' W' mem' a (Q + 1) /\
    PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W') mem') a (run_at tb text p Q) /\
    PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Q + 2) d tb /\
    wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
    rd_text tfibsegs B ly' S' W' mem' text len tcap /\
    fs_glob tfibsegs W' mem' (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail.
Definition ps2_POST : world tfibsegs -> config -> Prop :=
  fpostU tfibsegs B ps2_STKw ot FS_PSTAT_FP regs ly S U W mem md EV_fuzz_malloc ps2_U2 ps2_PQ.
(* the copy loop's head 0x85678 after i copied bytes, as machine facts *)
Definition ps2_LH (i : Z) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) : Prop :=
  spZ regsL = spZ regs - FRAME_PSTR /\
  YK11.getr regsL 3 = YK11.getr regs 3 /\ YK11.getr regsL 4 = YK11.getr regs 4 /\
  YK11.getr regsL 8 = w64 q /\ YK11.getr regsL 9 = w64 (q + 8) /\
  YK11.getr regsL 18 = w64 a /\ YK11.getr regsL 19 = w64 (a + i) /\ YK11.getr regsL 20 = w64 (p + 1 + i) /\
  YK11.getr regsL 22 = w64 (SHADOW_OFF + q / 8) /\ YK11.getr regsL 23 = w64 SHADOW_OFF /\
  YK11.getr regsL 24 = w64 (SHADOW_OFF + (q + 8) / 8) /\
  YK11.getr regsL 25 = w64 34 /\ YK11.getr regsL 14 = w64 32 /\ YK11.getr regsL 27 = w64 92 /\
  YK11.getr regsL 26 = w64 18446744073709551615 /\
  pstr_frame_at W2 memL regs (spZ regs - FRAME_PSTR) /\
  ajournal tfibsegs B ps2_STKw ot FS_PSTAT_FP ly S W (unpoison U mem) md [] ly2 S2 W2 (unpoison ps2_U2 memL) mdL
    EV_fuzz_malloc /\
  ARU tfibsegs B ly2 S2 ps2_U2 W2 memL mdL /\
  (forall x : word, ~ (a <= bv_unsigned x < a + i) -> ~ (spZ regs - FRAME_PSTR <= bv_unsigned x < spZ regs) ->
     memL x = mem2 x) /\
  (forall j, 0 <= j < i -> mbyte tfibsegs (mrestrict (w_H W2) memL) (a + j) = nth_error tb (Z.to_nat (p + 1 + j - text))).

(* ---- the numeric facts of the premises ---- *)
Lemma ps2_nums : 0 <= Q /\ p + 1 + Q < text + len /\ text <= p /\ text + len < 2 ^ 62 /\ q mod 8 = 0 /\
  Z.of_nat (length tb) = len /\ 4096 + HEAD <= text /\ len < tcap /\ text mod 16 = 0 /\
  In (text - HEAD, tcap + HEAD) (ablocks B ly2 S2) /\ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly2 S2) /\
  STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v) /\ alloc_ceiling <= spZ regs - STK_parse_string /\ spZ regs <= 2 ^ 47 /\
  140735332483072 <= alloc_ceiling <= 140737479966720 /\ kHighMemBeg = 17594333495296.
Proof.
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
pose proof Hrun as (R0 & R1 & _). pose proof HTX2 as (T0 & (T1 & T2 & T3 & _) & T4).
pose proof asan_consts as (C1 & _ & C3 & _).
assert (Hin : In (a - HEAD, Q + 1 + HEAD) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (E : STK_parse_string = ltac:(let v := eval vm_compute in STK_parse_string in exact v)) by (vm_compute; reflexivity).
repeat split; try assumption; lia.
Qed.
Lemma ps2_text_byte : forall k, 0 <= k < len ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) (text + k) = nth_error tb (Z.to_nat k).
Proof.
intros k Hk. pose proof ps2_nums as (_ & _ & _ & _ & _ & Hl & _).
pose proof HIN2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & Hb) & _).
specialize (Hb (Z.to_nat k) ltac:(lia)). rewrite Z2Nat.id in Hb by lia. exact Hb.
Qed.
(* the copy's bytes are writable on the machine's memory (live block bytes, no head covers them) *)
Lemma ps2_heap_wr : forall memX mdX x, ARU tfibsegs B ly2 S2 ps2_U2 W2 memX mdX -> a <= x < a + Q + 1 ->
  writable_at tfibsegs (mrestrict (w_H W2) memX) x.
Proof.
intros memX mdX x HARU Hx. pose proof ps2_nums as (N0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hin & _ & _ & _ & C1 & C3).
pose proof HARU as (HAR & _ & _). pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (al_blocks _ _ LAWS ly2 S2 W2 _ mdX _ _ HAR Hin) as (_ & _ & _ & _ & Hpres & _).
rewrite ps2_req in Hpres by (unfold HEAD; lia).
destruct (Hpres x ltac:(unfold HEAD in *; lia)) as [(Hh & b & Hb) _].
apply apresent_writable. split; [exact Hh|]. exists b. rewrite <- Hb. symmetry. apply unpoison_out.
rewrite (wz x ltac:(unfold HEAD in *; lia)). destruct (in_ush ps2_U2 x) eqn:Eu; [exfalso|reflexivity].
pose proof (ush_facts tfibsegs B ly2 S2 ps2_U2 W2 memX mdX x HARU Eu) as (_ & L1 & L2).
unfold HEAD, kLowShadowBeg, SHADOW_OFF in *. lia.
Qed.
(* in->end on the loop's memory *)
Lemma ps2_in_end : forall memL, (forall y, q <= y < q + 24 -> memL (Z_to_bv 64 y) = mem2 (Z_to_bv 64 y)) ->
  val_mem tfibsegs (mrestrict (w_H W2) memL) (q + 8) 8 (text + len).
Proof.
intros memL HM. pose proof ps2_nums as (_ & _ & _ & HT & _).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
pose proof HIN2 as (_ & Hend & _).
apply (pstr_val_mem_eq_at _ mem2 memL); [intros k Hk; apply HM; lia|].
apply (proj2 (val_mem_word_mem tfibsegs _ _ _)).
pose proof (KindBGlue.bytes_at_le8_word tfibsegs _ _ _ Hend) as Hw. rewrite unsigned_lit_small in Hw by lia. exact Hw.
Qed.
Lemma ps2_reg_keep : forall (H : word -> bool) E ss ms (r : bv 5) (n : nat) regsL extra,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> ew E n = ew (Ereg regsL extra) n ->
  Z.of_nat n = bv_unsigned r -> YK11.getr (ms_regs ms) r = YK11.getr regsL r.
Proof.
intros H E ss ms r n regsL extra HS Hr Hn Hnr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr, fsw_SOff0, Hn.
exact (ew_Ereg_nat regsL extra n r Hnr).
Qed.
Lemma ps2_spZ : forall regs0 v, YK11.getr regs0 2 = w64 v -> 0 <= v < 2 ^ 64 -> spZ regs0 = v.
Proof. intros regs0 v H Hv. unfold spZ. rewrite H. unfold w64. apply unsigned_lit_small; exact Hv. Qed.

Ltac ps2_ews := repeat rewrite ew_ewset_other by lia.
Ltac ps2_ews_in H := repeat rewrite ew_ewset_other in H by lia.

(* ---- one turn of the copy loop: byte i is plain, copied to a + i, and the loop goes back to 0x85678 ---- *)
Lemma ps2_step : forall i regsL memL mdL, 0 <= i < Q -> ps2_LH i regsL memL mdL ->
  (forall regs' mem' md', ps2_LH (i + 1) regs' mem' md' ->
     SRr tfibsegs W2 (mkCfg (YK11.mkst regs' (Z_to_bv 64 0x85678) mem' (YK11.seg_rom tfibsegs)) md') ps2_POST) ->
  SRr tfibsegs W2 (mkCfg (YK11.mkst regsL (Z_to_bv 64 0x85678) memL (YK11.seg_rom tfibsegs)) mdL) ps2_POST.
Proof.
intros i regsL memL mdL Hi HL HK.
destruct HL as (Lsp & L3 & L4 & L8 & L9 & L18 & L19 & L20 & L22 & L23 & L24 & L25 & L14 & L27 & L26 & LF & HJ & HARU &
  LM & LB).
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
assert (EH : HEAD = 16) by reflexivity. assert (ESO : SHADOW_OFF = 2147450880) by reflexivity.
assert (EFP : FRAME_PSTR = 144) by reflexivity. assert (ELS : kLowShadowBeg = 2147446784) by reflexivity.
pose proof Hrun as (_ & _ & _ & Hpl). destruct (Hpl i Hi) as (c & Hcb & Hcp). unfold plain_byte in Hcp.
pose proof (YK11.u8_range c) as Hc8.
assert (EW32 : ew (Ereg regsL [w64 (bv_unsigned c); w64 (text + len)]) 32 = w64 (bv_unsigned c)) by reflexivity.
assert (EW33 : ew (Ereg regsL [w64 (bv_unsigned c); w64 (text + len)]) 33 = w64 (text + len)) by reflexivity.
set (xs := [w64 (bv_unsigned c); w64 (text + len)]) in EW32, EW33.
assert (E2 : bv_unsigned (ew (Ereg regsL xs) 2) = spZ regs - FRAME_PSTR)
  by (rewrite (ew_Ereg_nat regsL xs 2 2%bv eq_refl); exact Lsp).
assert (E8 : bv_unsigned (ew (Ereg regsL xs) 8) = q) by (apply (ps2_ewR _ _ 8 8%bv); [reflexivity | exact L8 | lia]).
assert (E9 : bv_unsigned (ew (Ereg regsL xs) 9) = q + 8) by (apply (ps2_ewR _ _ 9 9%bv); [reflexivity | exact L9 | lia]).
assert (E18 : bv_unsigned (ew (Ereg regsL xs) 18) = a) by (apply (ps2_ewR _ _ 18 18%bv); [reflexivity | exact L18 | lia]).
assert (E19 : bv_unsigned (ew (Ereg regsL xs) 19) = a + i)
  by (apply (ps2_ewR _ _ 19 19%bv); [reflexivity | exact L19 | lia]).
assert (E20 : bv_unsigned (ew (Ereg regsL xs) 20) = p + 1 + i)
  by (apply (ps2_ewR _ _ 20 20%bv); [reflexivity | exact L20 | lia]).
assert (E23 : bv_unsigned (ew (Ereg regsL xs) 23) = SHADOW_OFF)
  by (apply (ps2_ewR _ _ 23 23%bv); [reflexivity | exact L23 | unfold SHADOW_OFF; lia]).
assert (E32 : bv_unsigned (ew (Ereg regsL xs) 32) = bv_unsigned c)
  by (rewrite EW32; unfold w64; apply unsigned_lit_small; lia).
assert (E33 : bv_unsigned (ew (Ereg regsL xs) 33) = text + len)
  by (rewrite EW33; unfold w64; apply unsigned_lit_small; lia).
assert (M2 : (spZ regs - FRAME_PSTR) mod 16 = 0)
  by (rewrite EFP; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact HSPal).
assert (M9 : (q + 8) mod 8 = 0) by (replace (q + 8) with (q + 1 * 8) by lia; rewrite Z_mod_plus_full; exact N4).
assert (HS : st_ok tfibsegs (Ereg regsL xs) ps2_ssL
  (restrict (w_H W2) (YK11.mkst regsL (Z_to_bv 64 0x85678) memL (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ps2_ssL. apply (entry_st_ok_full tfibsegs).
  - unfold ps2_srL.
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 8 q E8 E23 ltac:(lia)); exact L22].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 9 (q + 8) E9 E23 ltac:(lia)); exact L24].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L26].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L27].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L14].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L25].
    apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ps2_rgL. constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E20.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (ps2_chunk1_ok _ _ _ _ _ c); [rewrite fsw_SOff0; exact EW32|].
      rewrite Z.add_0_r. rewrite (ps2_mbyte_eq _ mem2 memL) by (apply LM; rewrite wz by lia; lia).
      replace (p + 1 + i) with (text + (p + 1 + i - text)) by lia. rewrite ps2_text_byte by lia.
      replace (text + (p + 1 + i - text)) with (p + 1 + i) by lia. exact Hcb.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E19.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (ps2_heap_wr memL mdL); [exact HARU | lia]|].
      constructor.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ (q + 8) 0 8 (SOff 33 0) (text + len));
        [rewrite fsw_SOff0; exact EW33 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
      cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. apply ps2_in_end.
      intros y Hy. apply LM; rewrite wz by lia; lia.
  - unfold ps2_rgL. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E19, E20, E9. repeat split; lia.
  - unfold ps2_faL. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E9, E19, E20, E23, E32, E33.
    repeat split; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | change (2 ^ 4) with 16; exact M2
      | change (2 ^ 3) with 8; first [exact N4 | exact M9]]. }
assert (SHOK : sh_ok tfibsegs ps2_Bq ps2_SHL (Ereg regsL xs) (mrestrict (w_H W2) memL)).
{ unfold sh_ok, ps2_SHL. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold ps2_Bq.
  rewrite (ps2_U_off _ 23 0 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
  rewrite (ps2_U_off _ 19 0 (a + i) E19) by lia. split.
  - rewrite !Z.add_0_r. replace (1 - 0) with 1 by lia.
    exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (a - HEAD) (Q + 1 + HEAD) (a + i) 1 HARU HFH HinA
      ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)).
  - intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy. lia. }
assert (HM : forall x : word, bv_unsigned x <> a + i -> memL x = memL x) by (intros; reflexivity).
(* run 1: to the `beq a2, s9` at 0x8568c *)
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold ps2_Bq. rewrite !U_SOff, E23, E20, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (text - HEAD) (tcap + HEAD) (p + 1 + i) 1 HARU HFH HinT
    ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) E19 HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* the closing quote? no: c <> 34 *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
{ exfalso. rewrite branch_eq_U, U_SOff, U_SLit in Hc. ps2_ews_in Hc. rewrite E32 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply Z.eqb_eq in Hc. lia. }
clear Hc.
(* run 2: to the `bne a1, s11` at 0x856a4 *)
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold ps2_Bq. rewrite !U_SOff. ps2_ews. rewrite E23, E20, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 _ _ (text - HEAD) (tcap + HEAD) (p + 1 + i) 1 HARU HFH HinT
    ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) ltac:(ps2_ews; exact E19) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* no escape: c <> 0x5c *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
2: { exfalso. rewrite branch_ne_U, U_SOff, U_SLit in Hc. ps2_ews_in Hc. rewrite E32 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply negb_false_iff, Z.eqb_eq in Hc. lia. }
clear Hc.
(* run 3: the UBSan tests, the store to a + i and the in->end reload, to the `bltu s5, a0` at 0x85764 *)
fsw_aj_run_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan.
{ unfold ps2_Bq. rewrite !U_SOff. ps2_ews. rewrite E23, E9, !Z.add_0_r.
  rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_stk_mem B ly2 S2 ps2_U2 W2 _ _ (q + 8) 8 HARU ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia)
    ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia) M9 eq_refl ltac:(lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) ltac:(ps2_ews; exact E19) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* the loop goes on: p + 1 + i + 1 < text + len *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
2: { exfalso. rewrite branch_ltu_U, !U_SOff in Hc. ps2_ews_in Hc. rewrite E20, E33 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. lia. }
clear Hc.
(* run 4: the taken branch back to the loop head *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x85678.
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
  split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia. }
pose proof (ps2_chain1 _ _ _ _ _ 19 (a + i) HF ltac:(vm_compute; reflexivity) ltac:(ps2_ews; exact E19) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
(* the copied byte *)
pose proof (fsw_region_nth _ _ _ 1 (YP09.mkRegion (Some 19%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))]) HS
  ltac:(vm_compute; reflexivity)) as RO.
pose proof (ps2_chunk1 _ _ _ _ _ _ _ _ 0 (SOff 32 0) RO ltac:(left; reflexivity)) as HB. clear RO.
rewrite fsw_SOff0 in HB. ps2_ews_in HB. rewrite E19, Z.add_0_r, EW32 in HB.
unfold w64 in HB. rewrite unsigned_lit_small, Z_to_bv_bv_unsigned in HB by lia.
pose proof (@st_ok_restrict_mkst tfibsegs _ (w_H W2) _ _ _ HS eq_refl) as Hshape. rewrite Hshape.
apply HK. unfold ps2_LH.
rewrite ?wvb_collapse in HJ, HARU.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj HJ (conj HARU (conj _ _))))))))))))))))))).
- apply ps2_spZ; [|lia]. apply (ps2_reg_val _ _ _ _ 2%bv (SOff 2 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (spZ regs - FRAME_PSTR)); [ps2_ews; exact E2 | lia | lia].
- rewrite (ps2_reg_keep _ _ _ _ 3%bv 3 regsL xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact L3.
- rewrite (ps2_reg_keep _ _ _ _ 4%bv 4 regsL xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact L4.
- apply (ps2_reg_val _ _ _ _ 8%bv (SOff 8 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ q); [ps2_ews; exact E8 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 9%bv (SOff 9 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (q + 8)); [ps2_ews; exact E9 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 18%bv (SOff 18 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E18 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 19%bv (SOff 19 1) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (a + i)); [ps2_ews; exact E19 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 20%bv (SOff 20 1) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (p + 1 + i)); [ps2_ews; exact E20 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 22%bv (ps2_shx 8) _ HS); [vm_compute; reflexivity|].
  apply ps2_shx_denot; [ps2_ews; exact E8 | ps2_ews; exact E23 | lia].
- apply (ps2_reg_val _ _ _ _ 23%bv (SOff 23 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ SHADOW_OFF); [ps2_ews; exact E23 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 24%bv (ps2_shx 9) _ HS); [vm_compute; reflexivity|].
  apply ps2_shx_denot; [ps2_ews; exact E9 | ps2_ews; exact E23 | lia].
- apply (ps2_reg_val _ _ _ _ 25%bv (SLit 34) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 14%bv (SLit 32) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 27%bv (SLit 92) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 26%bv (SLit 18446744073709551615) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_frame_keep W2 memL); [lia | lia | | exact LF]. intros y Hy. apply HM. rewrite wz by lia. lia.
- intros x Hx1 Hx2. rewrite (HM x ltac:(lia)). apply LM; lia.
- intros j Hj. destruct (Z.eq_dec j i) as [->|Hne].
  + rewrite Hcb. exact HB.
  + rewrite (ps2_mbyte_eq _ memL) by (apply HM; rewrite wz by lia; lia). apply LB. lia.
Qed.

(* ---- the post's memory facts from the final memory: it is mem2 outside the copy [a, a + Q], the frame and in->p ---- *)
Lemma ps2_post : forall regsF memF mdF,
  (forall x : word, ~ (a <= bv_unsigned x < a + Q + 1) -> ~ (spZ regs - FRAME_PSTR <= bv_unsigned x < spZ regs) ->
     ~ (q <= bv_unsigned x < q + 8) -> memF x = mem2 x) ->
  (forall j, 0 <= j < Q ->
     mbyte tfibsegs (mrestrict (w_H W2) memF) (a + j) = nth_error tb (Z.to_nat (p + 1 + j - text))) ->
  mbyte tfibsegs (mrestrict (w_H W2) memF) (a + Q) = Some (Z_to_bv 8 0) ->
  val_mem tfibsegs (mrestrict (w_H W2) memF) q 8 (p + Q + 2) ->
  (forall o, 0 <= o < 8 -> writable_at tfibsegs (mrestrict (w_H W2) memF) (q + o)) ->
  YK11.getr regsF 10 = w64 a ->
  ps2_PQ ly2 S2 W2 regsF memF mdF.
Proof.
intros regsF memF mdF HMF HBY HNUL HP HPW H10.
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
pose proof Hrun as (_ & _ & _ & Hpl).
assert (EH : HEAD = 16) by reflexivity. assert (EFP : FRAME_PSTR = 144) by reflexivity.
assert (KEEP : forall y, 0 <= y < 2 ^ 64 -> ~ (a <= y < a + Q + 1) -> ~ (spZ regs - FRAME_PSTR <= y < spZ regs) ->
  ~ (q <= y < q + 8) -> memF (Z_to_bv 64 y) = mem2 (Z_to_bv 64 y)).
{ intros y Hy H1 H2 H3. apply HMF; rewrite wz by lia; lia. }
set (k0 := Z.to_nat (p + 1 - text)).
assert (RUN : forall j, (j < Z.to_nat Q)%nat ->
  nth_error (firstn (Z.to_nat Q) (skipn k0 tb)) j = nth_error tb (Z.to_nat (p + 1 + Z.of_nat j - text))).
{ intros j Hj. rewrite nth_error_firstn. replace (j <? Z.to_nat Q)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
  rewrite nth_error_skipn. f_equal. unfold k0. lia. }
assert (LRUN : length (firstn (Z.to_nat Q) (skipn k0 tb)) = Z.to_nat Q).
{ apply firstn_length_le. rewrite length_skipn. unfold k0. lia. }
unfold ps2_PQ.
split; [exact H10|]. split; [exact Ha16|]. split; [exact Hab|].
split.
{ destruct HRB as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  apply (pstr_val_mem_eq_at _ mem2 memF); [|exact R4]. intros k Hk. apply KEEP; lia. }
split.
{ unfold PjStruct.pj_cbytes, run_at, ReaderRes.zb. fold k0. split.
  - apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
    apply In_nth_error in Hb as (j & Hj).
    assert (Hjl : (j < Z.to_nat Q)%nat) by (rewrite <- LRUN; apply nth_error_Some; congruence).
    rewrite (RUN j Hjl) in Hj. destruct (Hpl (Z.of_nat j) ltac:(lia)) as (c' & Hc' & Hpc').
    rewrite Hj in Hc'. injection Hc' as <-. unfold plain_byte in Hpc'. pose proof (YK11.u8_range b). lia.
  - split; [lia|]. rewrite length_map, length_app, length_map, LRUN. cbn [length]. split; [lia|].
    intros j Hj. rewrite nth_error_map. destruct (Nat.lt_ge_cases j (Z.to_nat Q)) as [Hjq|Hjq].
    + rewrite nth_error_app1 by (rewrite length_map, LRUN; lia). rewrite nth_error_map, RUN by exact Hjq.
      transitivity (mbyte tfibsegs (mrestrict (w_H W2) memF) (a + Z.of_nat j)); [reflexivity|].
      rewrite HBY by lia. destruct (Hpl (Z.of_nat j) ltac:(lia)) as (c' & Hc' & _). rewrite Hc'. cbn [option_map].
      rewrite Z_to_bv_bv_unsigned. reflexivity.
    + assert (j = Z.to_nat Q) by lia. subst j.
      rewrite nth_error_app2 by (rewrite length_map, LRUN; lia). rewrite length_map, LRUN, Nat.sub_diag.
      cbn [nth_error option_map].
      transitivity (mbyte tfibsegs (mrestrict (w_H W2) memF) (a + Z.of_nat (Z.to_nat Q))); [reflexivity|].
      rewrite Z2Nat.id by lia. exact HNUL. }
split.
{ destruct HIN2 as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12).
  refine (conj _ (conj _ (conj _ (conj _ (conj I5 (conj I6 (conj I7 (conj _ (conj I9 (conj _ (conj I11 I12))))))))))).
  - apply KindBGlue.word_mem_le8; [apply val_mem_word_mem; exact HP | lia | lia | lia].
  - apply (ps2_bytes_at_eq _ mem2 memF); [|exact I2]. intros k Hk. rewrite lib.Lib.Mem.length_le8 in Hk.
    apply KEEP; lia.
  - apply (ps2_bytes_at_eq _ mem2 memF); [|exact I3]. intros k Hk. rewrite lib.Lib.Mem.length_le4 in Hk.
    apply KEEP; lia.
  - destruct I4 as (W1 & W1' & W3). split; [lia|]. split; [lia|]. intros o Ho.
    destruct (Z_lt_le_dec o 8) as [Ho8|Ho8]; [exact (HPW o ltac:(lia))|].
    apply (ps2_wr_eq _ mem2 memF (q + o)); [apply KEEP; lia | exact (W3 o Ho)].
  - lia.
  - apply (ps2_bytes_at_eq _ mem2 memF); [|exact I10]. intros k Hk. apply KEEP; lia. }
split.
{ intros x Hx Hnq. destruct (HWK x Hx Hnq) as [K1 K2].
  assert (Ex : memF (Z_to_bv 64 x) = mem2 (Z_to_bv 64 x)) by (apply KEEP; lia).
  split; [rewrite (ps2_mbyte_eq _ mem2 memF x Ex); exact K1|].
  rewrite K2. exact (ps2_wr_eq _ mem2 memF x Ex). }
split.
{ destruct HTX2 as (T0 & (T1 & T2 & T3 & T4) & T5). split; [exact T0|]. split; [|exact T5].
  split; [exact T1|]. split; [exact T2|]. split; [exact T3|].
  apply (pstr_val_mem_eq_at _ mem2 memF); [|exact T4]. intros k Hk. apply KEEP; lia. }
assert (GK : forall g v, 0xa1000 <= g -> g + 8 <= 0x5fd000 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) g 8 v -> val_mem tfibsegs (mrestrict (w_H W2) memF) g 8 v).
{ intros g v Hg1 Hg2 Hv. apply (pstr_val_mem_eq_at _ mem2 memF); [|exact Hv]. intros k Hk. apply KEEP; [lia | | lia | lia].
  intros Hin. apply (Himg (g + Z.of_nat k)); [lia | apply ps2_img_hi; lia]. }
destruct HGL as (G1 & G2 & G3 & G4 & GR). cbv [fs_glob fs_glob_at].
split; [apply GK; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact G1]|].
split; [apply GK; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact G2]|].
split; [apply GK; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact G3]|].
split; [apply GK; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact G4]|].
exact GR.
Qed.

(* ---- the exit: the byte at the read cursor is the closing quote; the NUL, in->p := p + Q + 2, the epilogue, `ret` ---- *)
Lemma ps2_exit : forall regsL memL mdL, ps2_LH Q regsL memL mdL ->
  SRr tfibsegs W2 (mkCfg (YK11.mkst regsL (Z_to_bv 64 0x85678) memL (YK11.seg_rom tfibsegs)) mdL) ps2_POST.
Proof.
intros regsL memL mdL HL.
destruct HL as (Lsp & L3 & L4 & L8 & L9 & L18 & L19 & L20 & L22 & L23 & L24 & L25 & L14 & L27 & L26 & LF & HJ & HARU &
  LM & LB).
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
assert (EH : HEAD = 16) by reflexivity. assert (ESO : SHADOW_OFF = 2147450880) by reflexivity.
assert (EFP : FRAME_PSTR = 144) by reflexivity. assert (ELS : kLowShadowBeg = 2147446784) by reflexivity.
pose proof Hrun as (_ & _ & Rq & _).
set (xs := ps2_xsX regs).
assert (E2 : bv_unsigned (ew (Ereg regsL xs) 2) = spZ regs - FRAME_PSTR)
  by (rewrite (ew_Ereg_nat regsL xs 2 2%bv eq_refl); exact Lsp).
assert (E8 : bv_unsigned (ew (Ereg regsL xs) 8) = q) by (apply (ps2_ewR _ _ 8 8%bv); [reflexivity | exact L8 | lia]).
assert (E9 : bv_unsigned (ew (Ereg regsL xs) 9) = q + 8) by (apply (ps2_ewR _ _ 9 9%bv); [reflexivity | exact L9 | lia]).
assert (E18 : bv_unsigned (ew (Ereg regsL xs) 18) = a) by (apply (ps2_ewR _ _ 18 18%bv); [reflexivity | exact L18 | lia]).
assert (E19 : bv_unsigned (ew (Ereg regsL xs) 19) = a + Q)
  by (apply (ps2_ewR _ _ 19 19%bv); [reflexivity | exact L19 | lia]).
assert (E20 : bv_unsigned (ew (Ereg regsL xs) 20) = p + 1 + Q)
  by (apply (ps2_ewR _ _ 20 20%bv); [reflexivity | exact L20 | lia]).
assert (E23 : bv_unsigned (ew (Ereg regsL xs) 23) = SHADOW_OFF)
  by (apply (ps2_ewR _ _ 23 23%bv); [reflexivity | exact L23 | unfold SHADOW_OFF; lia]).
assert (M2 : (spZ regs - FRAME_PSTR) mod 16 = 0)
  by (rewrite EFP; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact HSPal).
pose proof LF as LF'. unfold pstr_frame_at, pstr_saved in LF'.
repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H; destruct H as [? H] end.
cbn [fst snd] in *.
assert (HS : st_ok tfibsegs (Ereg regsL xs) ps2_ssX
  (restrict (w_H W2) (YK11.mkst regsL (Z_to_bv 64 0x85678) memL (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ps2_ssX. apply (entry_st_ok_full tfibsegs).
  - unfold ps2_srL.
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 8 q E8 E23 ltac:(lia)); exact L22].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 9 (q + 8) E9 E23 ltac:(lia)); exact L24].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L26].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L27].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L14].
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz | rewrite ps2_denot_lit by lia; exact L25].
    apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ps2_rgX. constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E20.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (ps2_chunk1_ok _ _ _ _ _ (Z_to_bv 8 34)); [rewrite ps2_denot_lit by lia; reflexivity|].
      rewrite Z.add_0_r. rewrite (ps2_mbyte_eq _ mem2 memL) by (apply LM; rewrite wz by lia; lia).
      replace (p + 1 + Q) with (text + (p + 1 + Q - text)) by lia. rewrite ps2_text_byte by lia.
      replace (text + (p + 1 + Q - text) - text) with (p + 1 + Q - text) in Rq by lia.
      replace (p + 1 + Q - text) with (p + 1 + Q - text) by lia. exact Rq.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E19.
      split; [lia|]. split; [lia|]. split; [intros o Ho; apply (ps2_heap_wr memL mdL); [exact HARU | lia]|].
      constructor.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E8.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho.
      pose proof HIN2 as (_ & _ & _ & (W1 & W1' & W3) & _).
      apply (ps2_wr_eq _ mem2 memL (q + o)); [apply LM; rewrite wz by lia; lia | exact (W3 o ltac:(lia))].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. unfold ps2_fchunks.
      repeat (apply Forall_cons; [eapply ps2_fchunk; [eassumption | rewrite fsw_SOff0, Z_to_bv_bv_unsigned; reflexivity
        | apply YK11.u64_range] |]).
      apply Forall_nil.
  - unfold ps2_rgX. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E19, E20, E8, E2. repeat split; lia.
  - unfold ps2_faX. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E8, E19, E20, E23.
    repeat split; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | change (2 ^ 4) with 16; exact M2
      | change (2 ^ 3) with 8; exact N4]. }
assert (SHOK : sh_ok tfibsegs ps2_Bq ps2_SHL (Ereg regsL xs) (mrestrict (w_H W2) memL)).
{ unfold sh_ok, ps2_SHL. constructor; [|constructor]. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi].
  unfold ps2_Bq.
  rewrite (ps2_U_off _ 23 0 SHADOW_OFF E23) by (unfold SHADOW_OFF; lia).
  rewrite (ps2_U_off _ 19 0 (a + Q) E19) by lia. split.
  - rewrite !Z.add_0_r. replace (1 - 0) with 1 by lia.
    exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (a - HEAD) (Q + 1 + HEAD) (a + Q) 1 HARU HFH HinA
      ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)).
  - intros y Hy. change (Z.min 0 1) with 0 in Hy. change (Z.max 0 1) with 1 in Hy. lia. }
(* one run: the closing quote, the NUL, in->p, the epilogue, to the `ret` at 0x85a5c *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x85a5c.
{ unfold ps2_Bq. rewrite !U_SOff, E23, E8, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_stk_mem B ly2 S2 ps2_U2 W2 _ _ q 8 HARU ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia)
    ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia) N4 eq_refl ltac:(lia)). }
{ unfold ps2_Bq. rewrite !U_SOff, E23, E20, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_blk_mem B ly2 S2 ps2_U2 W2 memL mdL (text - HEAD) (tcap + HEAD) (p + 1 + Q) 1 HARU HFH HinT
    ltac:(unfold HEAD; lia) ltac:(lia) ltac:(rewrite ps2_req by (unfold HEAD; lia); unfold HEAD; lia)). }
{ apply (ps2_awr_wins _ _ [(19%nat, 0, 1); (8%nat, 0, 8)]); [vm_compute; reflexivity|].
  constructor; [|constructor; [|constructor]]; cbn [fst snd]; intros x Hx.
  - rewrite E19 in Hx. left; right; right; left. exists (a - HEAD), (Q + 1 + HEAD).
    split; [exact HinA|]. split; [exact Hnew|]. rewrite ps2_req by (unfold HEAD; lia). unfold HEAD in *. lia.
  - rewrite E8 in Hx. left; left. unfold ps2_STKw. lia. }
match goal with HS0 : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msf end.
assert (HMF : forall x : word, ~ (a + Q <= bv_unsigned x < a + Q + 1) -> ~ (q <= bv_unsigned x < q + 8) ->
  ms_mem msf x = memL x).
{ intros x Hy1 Hy2. refine (ps2_frame_wins _ _ _ _ [(19%nat, 0, 1); (8%nat, 0, 8)] _ HF x _); [vm_compute; reflexivity|].
  constructor; [|constructor; [|constructor]]; cbn [fst snd]; [rewrite E19 | rewrite E8]; lia. }
pose proof (fsw_region_nth _ _ _ 1 (YP09.mkRegion (Some 19%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS
  ltac:(vm_compute; reflexivity)) as RO.
pose proof (ps2_chunk1 _ _ _ _ _ _ _ _ 0 (SLit 0) RO ltac:(left; reflexivity)) as HB0. clear RO.
ps2_ews_in HB0. rewrite E19, Z.add_0_r, ps2_denot_lit in HB0 by lia. unfold w64 in HB0.
rewrite unsigned_lit_small in HB0 by lia.
pose proof (fsw_region_nth _ _ _ 2 (YP09.mkRegion (Some 8%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 20 1))]) HS
  ltac:(vm_compute; reflexivity)) as RP.
pose proof (fsw_field _ _ _ q _ _ _ _ _ 0 8 (SOff 20 1) (p + Q + 2) RP ltac:(ps2_ews; exact E8)
  ltac:(left; reflexivity) ltac:(apply (ps2_denot_off _ _ _ (p + 1 + Q)); [ps2_ews; exact E20 | lia | lia])
  ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)) as HPV.
rewrite Z.add_0_r in HPV.
destruct RP as (_ & _ & RPW & _). cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in RPW. ps2_ews_in RPW.
rewrite E8 in RPW.
unfold ps2_POST.
refine (fsw_retU B parse_string_tbl parse_string_tbl_ok W2 _ _ msf _ ps2_STKw ot FS_PSTAT_FP regs ly S U W mem md
  ly2 S2 ps2_U2 EV_fuzz_malloc ps2_PQ HS eq_refl ltac:(vm_compute; reflexivity) _ HJ HARU _ _).
- rewrite (st_ok_restrict_reg tfibsegs _ _ _ msf 1%bv HS).
  match goal with |- context [sr_get ?l 1%bv] => replace (sr_get l 1%bv) with (SOff 32 0) by (vm_compute; reflexivity) end.
  rewrite fsw_SOff0. ps2_ews. exact Hra.
- apply (fsw_preserved _ _ _ msf regs ps2_expect HS); [vm_compute; reflexivity|].
  intros r Hr. cbv [CALLEE_SAVED In] in Hr. repeat (destruct Hr as [<-|Hr]); [..|destruct Hr].
  all: lazymatch goal with |- sv_denot _ (ps2_expect ?r) = _ =>
    let e := eval vm_compute in (ps2_expect r) in change (ps2_expect r) with e end.
  all: first
    [ rewrite fsw_SOff0; ps2_ews; reflexivity
    | rewrite fsw_SOff0; ps2_ews; rewrite (ew_Ereg_nat regsL xs 3 3%bv eq_refl); exact L3
    | rewrite fsw_SOff0; ps2_ews; rewrite (ew_Ereg_nat regsL xs 4 4%bv eq_refl); exact L4
    | apply bv_eq; rewrite denot_SOff; ps2_ews; rewrite E2; change (bv_unsigned (YK11.getr regs 2%bv)) with (spZ regs);
      rewrite zcanon_id by (unfold M64; lia); lia ].
- intros mat0. apply ps2_post.
  + intros x Hx1 Hx2 Hx3. rewrite (HMF x ltac:(lia) Hx3). apply LM; lia.
  + intros j Hj. rewrite (ps2_mbyte_eq _ memL) by (apply HMF; rewrite wz by lia; lia). apply LB. lia.
  + exact HB0.
  + exact HPV.
  + intros o Ho. exact (RPW o Ho).
  + apply (ps2_reg_val _ _ _ _ 10%bv (SOff 18 0) _ HS); [vm_compute; reflexivity|].
    apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E18 | lia | lia].
Qed.

(* ---- the copy loop: induction over the bytes left ---- *)
Lemma ps2_loop : forall n i regsL memL mdL, Z.to_nat (Q - i) = n -> 0 <= i <= Q -> ps2_LH i regsL memL mdL ->
  SRr tfibsegs W2 (mkCfg (YK11.mkst regsL (Z_to_bv 64 0x85678) memL (YK11.seg_rom tfibsegs)) mdL) ps2_POST.
Proof.
induction n as [|n IH]; intros i regsL memL mdL Hn Hi HL.
- assert (i = Q) by lia. subst i. exact (ps2_exit regsL memL mdL HL).
- apply (ps2_step i regsL memL mdL ltac:(lia) HL). intros regs' mem' md' HL'.
  apply (IH (i + 1) regs' mem' md'); [lia | lia | exact HL'].
Qed.

(* ---- from the return of fuzz_malloc 0x85618 to the loop head 0x85678 (the a0 test, in->end, the constants) ---- *)
Lemma ps2_r0 : forall regs2 md2,
  spZ regs2 = spZ regs - FRAME_PSTR -> YK11.getr regs2 10 = w64 a ->
  YK11.getr regs2 3 = YK11.getr regs 3 -> YK11.getr regs2 4 = YK11.getr regs 4 ->
  YK11.getr regs2 8 = w64 q -> YK11.getr regs2 9 = w64 (q + 8) -> YK11.getr regs2 20 = w64 (p + 1) ->
  YK11.getr regs2 22 = w64 (SHADOW_OFF + q / 8) -> YK11.getr regs2 23 = w64 SHADOW_OFF ->
  YK11.getr regs2 24 = w64 (SHADOW_OFF + (q + 8) / 8) ->
  pstr_frame_at W2 mem2 regs (spZ regs - FRAME_PSTR) ->
  ajournal tfibsegs B ps2_STKw ot FS_PSTAT_FP ly S W (unpoison U mem) md [] ly2 S2 W2 (unpoison ps2_U2 mem2) md2
    EV_fuzz_malloc ->
  ARU tfibsegs B ly2 S2 ps2_U2 W2 mem2 md2 ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2) ps2_POST.
Proof using All.
intros regs2 md2 Rsp R10 R3 R4 R8 R9 R20 R22 R23 R24 RF HJ HARU.
pose proof ps2_nums as (N0 & N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & HinT & HinA & NSTK & N9 & N10 & C1 & C3).
pose proof (PjIn.pj_in_ok_bounds tfibsegs _ _ _ _ _ _ _ HIN2) as (B0 & B1 & B2 & B3 & _).
assert (EH : HEAD = 16) by reflexivity. assert (ESO : SHADOW_OFF = 2147450880) by reflexivity.
assert (EFP : FRAME_PSTR = 144) by reflexivity.
set (xs := [w64 (text + len)]).
assert (EW32 : ew (Ereg regs2 xs) 32 = w64 (text + len)) by reflexivity.
assert (E2 : bv_unsigned (ew (Ereg regs2 xs) 2) = spZ regs - FRAME_PSTR)
  by (rewrite (ew_Ereg_nat regs2 xs 2 2%bv eq_refl); exact Rsp).
assert (E8 : bv_unsigned (ew (Ereg regs2 xs) 8) = q) by (apply (ps2_ewR _ _ 8 8%bv); [reflexivity | exact R8 | lia]).
assert (E9 : bv_unsigned (ew (Ereg regs2 xs) 9) = q + 8) by (apply (ps2_ewR _ _ 9 9%bv); [reflexivity | exact R9 | lia]).
assert (E10 : bv_unsigned (ew (Ereg regs2 xs) 10) = a) by (apply (ps2_ewR _ _ 10 10%bv); [reflexivity | exact R10 | lia]).
assert (E20 : bv_unsigned (ew (Ereg regs2 xs) 20) = p + 1)
  by (apply (ps2_ewR _ _ 20 20%bv); [reflexivity | exact R20 | lia]).
assert (E23 : bv_unsigned (ew (Ereg regs2 xs) 23) = SHADOW_OFF)
  by (apply (ps2_ewR _ _ 23 23%bv); [reflexivity | exact R23 | lia]).
assert (E32 : bv_unsigned (ew (Ereg regs2 xs) 32) = text + len)
  by (rewrite EW32; unfold w64; apply unsigned_lit_small; lia).
assert (M2 : (spZ regs - FRAME_PSTR) mod 16 = 0)
  by (rewrite EFP; replace (spZ regs - 144) with (spZ regs + (-9) * 16) by lia; rewrite Z_mod_plus_full; exact HSPal).
assert (M9 : (q + 8) mod 8 = 0) by (replace (q + 8) with (q + 1 * 8) by lia; rewrite Z_mod_plus_full; exact N4).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (HS : st_ok tfibsegs (Ereg regs2 xs) ps2_ss0
  (restrict (w_H W2) (YK11.mkst regs2 (Z_to_bv 64 0x85618) mem2 (YK11.seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ps2_ss0. apply (entry_st_ok_full tfibsegs).
  - unfold ps2_sr0.
    apply regs_ok_pin; [| apply ps2_nz; vm_compute; intro Hz; discriminate Hz
      | rewrite (ps2_shx_denot _ 9 (q + 8) E9 E23 ltac:(lia)); exact R24].
    apply regs_ok_Ereg.
  - vm_compute. reflexivity.
  - unfold ps2_rg0. constructor; [|constructor; [|constructor]].
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E2.
      split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply (apresent_writable tfibsegs).
      apply (fsw_apresent_unpoison B ly2 S2 ps2_U2 W2 mem2 md2 _ HARU); [lia|]. apply Hpres. unfold ps2_STKw. lia.
    + unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val tfibsegs _ _ (q + 8) 0 8 (SOff 32 0) (text + len));
        [rewrite fsw_SOff0; exact EW32 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia |].
      cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]. rewrite Z.add_0_r. apply ps2_in_end. intros y Hy. reflexivity.
  - unfold ps2_rg0. cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E9. repeat split; lia.
  - unfold ps2_fa0. split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E2, E9, E10, E20, E23, E32.
    repeat split; first [lia | rewrite Z.pow_0_r, Z.mod_1_r; reflexivity | change (2 ^ 4) with 16; first [exact M2 | exact Ham]
      | change (2 ^ 3) with 8; exact M9]. }
assert (SHOK : sh_ok tfibsegs ps2_Bq [] (Ereg regs2 xs) (mrestrict (w_H W2) mem2)) by constructor.
change (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2)
  with (mkCfg (YK11.mkst regs2 (Z_to_bv 64 0x85618) mem2 (YK11.seg_rom tfibsegs)) md2).
(* run 1: to the `bgeu s4, a0` at 0x8562c *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x85678.
{ unfold ps2_Bq. rewrite !U_SOff, E23, E9, !Z.add_0_r. rewrite !zcanon_id by (unfold M64, SHADOW_OFF; lia).
  exact (pstr_RA_stk_mem B ly2 S2 ps2_U2 W2 _ _ (q + 8) 8 HARU ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia)
    ltac:(rewrite Hlo2; lia) ltac:(rewrite Hhi2; lia) M9 eq_refl ltac:(lia)). }
{ apply (ps2_awr_wins _ _ [(2%nat, 8, 32)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. rewrite E2 in Hx. left; left. unfold ps2_STKw. lia. }
assert (HM0 : forall x : word, ~ (spZ regs - FRAME_PSTR + 8 <= bv_unsigned x < spZ regs - FRAME_PSTR + 32) ->
  mem2 x = mem2 x) by (intros; reflexivity).
pose proof (ps2_chainw _ _ _ _ _ 2 8 32 (spZ regs - FRAME_PSTR) HF ltac:(vm_compute; reflexivity) E2 HM0) as HM.
clear HF HFr HG HM0.
(* in->end is past the read cursor *)
srr_branch_tok parse_string_tbl_ok HS SHOK fs_Bspan.
{ exfalso. rewrite branch_geu_U, !U_SOff in Hc. ps2_ews_in Hc. rewrite E20, E32 in Hc.
  rewrite !zcanon_id in Hc by (unfold M64; lia). apply negb_true_iff, Z.ltb_ge in Hc. lia. }
clear Hc.
(* run 2: the constants, the three frame slots, s3 := a, to the loop head *)
fsw_aj_run_to_tokU parse_string_tbl_ok HS HJ HARU SHOK fs_Bspan 0x85678.
{ apply (ps2_awr_wins _ _ [(2%nat, 8, 32)]); [vm_compute; reflexivity|]. constructor; [|constructor].
  cbn [fst snd]. intros x Hx. ps2_ews_in Hx. rewrite E2 in Hx. left; left. unfold ps2_STKw. lia. }
pose proof (ps2_chainw _ _ _ _ _ 2 8 32 (spZ regs - FRAME_PSTR) HF ltac:(vm_compute; reflexivity)
  ltac:(ps2_ews; exact E2) HM) as HM'.
clear HF HFr HG HM. rename HM' into HM.
pose proof (@st_ok_restrict_mkst tfibsegs _ (w_H W2) _ _ _ HS eq_refl) as Hshape. rewrite Hshape.
rewrite ?wvb_collapse in HJ, HARU.
apply (ps2_loop (Z.to_nat (Q - 0)) 0); [reflexivity | lia |]. unfold ps2_LH.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj _ (conj HJ (conj HARU (conj _ _))))))))))))))))))).
- apply ps2_spZ; [|lia]. apply (ps2_reg_val _ _ _ _ 2%bv (SOff 2 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (spZ regs - FRAME_PSTR)); [ps2_ews; exact E2 | lia | lia].
- rewrite (ps2_reg_keep _ _ _ _ 3%bv 3 regs2 xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact R3.
- rewrite (ps2_reg_keep _ _ _ _ 4%bv 4 regs2 xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact R4.
- apply (ps2_reg_val _ _ _ _ 8%bv (SOff 8 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ q); [ps2_ews; exact E8 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 9%bv (SOff 9 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (q + 8)); [ps2_ews; exact E9 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 18%bv (SOff 10 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E10 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 19%bv (SOff 10 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ a); [ps2_ews; exact E10 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 20%bv (SOff 20 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ (p + 1)); [ps2_ews; exact E20 | lia | lia].
- rewrite (ps2_reg_keep _ _ _ _ 22%bv 22 regs2 xs HS ltac:(vm_compute; reflexivity) ltac:(ps2_ews; reflexivity) eq_refl).
  exact R22.
- apply (ps2_reg_val _ _ _ _ 23%bv (SOff 23 0) _ HS); [vm_compute; reflexivity|].
  apply (ps2_denot_off _ _ _ SHADOW_OFF); [ps2_ews; exact E23 | lia | lia].
- apply (ps2_reg_val _ _ _ _ 24%bv (ps2_shx 9) _ HS); [vm_compute; reflexivity|].
  apply ps2_shx_denot; [ps2_ews; exact E9 | ps2_ews; exact E23 | lia].
- apply (ps2_reg_val _ _ _ _ 25%bv (SLit 34) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 14%bv (SLit 32) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 27%bv (SLit 92) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_reg_val _ _ _ _ 26%bv (SLit 18446744073709551615) _ HS); [vm_compute; reflexivity | apply ps2_denot_lit; lia].
- apply (ps2_frame_keep W2 mem2); [lia | lia | | exact RF]. intros y Hy. apply HM. rewrite wz by lia. lia.
- intros x Hx1 Hx2. apply HM. lia.
- intros j Hj. lia.
Qed.

End L.

(* ---- the new block against the blocks of the entry (AR at the return) ---- *)
Lemma ps2_blocks : forall ly S ly2 S2 (W2 : world tfibsegs) mem2 md2 text tcap a Q,
  AR tfibsegs B ly2 S2 W2 mem2 md2 ->
  ablocks B ly2 S2 = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] ->
  In (text - HEAD, tcap + HEAD) (ablocks B ly S) -> 0 <= Q -> 0 < tcap ->
  ~ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly S) /\
  (text + tcap <= a - HEAD \/ a + Q + 1 <= text - HEAD) /\
  a + Q + 1 <= alloc_ceiling /\ text + tcap <= alloc_ceiling /\
  (a + Q + 1 <= kLowShadowBeg \/ kHighMemBeg <= a - HEAD) /\
  (forall x, a - HEAD <= x < a + Q + 1 -> ~ in_img tfibsegs x).
Proof.
intros ly S ly2 S2 W2 mem2 md2 text tcap a Q HAR Hab HT HQ Htc.
pose proof (AR_laws_ok tfibsegs B) as LAWS. assert (EH : HEAD = 16) by reflexivity.
assert (HinA : In (a - HEAD, Q + 1 + HEAD) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; right; left; reflexivity).
assert (HinT : In (text - HEAD, tcap + HEAD) (ablocks B ly2 S2)) by (rewrite Hab; apply in_or_app; left; exact HT).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinA) as (_ & _ & Ca & Appa & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR HinT) as (_ & _ & Ct & _).
rewrite ps2_req in Ca, Appa by lia. rewrite ps2_req in Ct by lia.
assert (Hnew : ~ In (a - HEAD, Q + 1 + HEAD) (ablocks B ly S)).
{ intros Hin. apply in_split in Hin as (l1 & l2 & E).
  pose proof (sep_blocks_pos tfibsegs B LAWS _ _ _ _ _ (a - HEAD, Q + 1 + HEAD) (a - HEAD, Q + 1 + HEAD) l1 l2 [] HAR
    ltac:(rewrite Hab, E, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd. rewrite ps2_req in Hd by lia. lia. }
split; [exact Hnew|].
split.
{ pose proof (sep_blocks tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR HinT HinA
    ltac:(intros Heq; apply Hnew; rewrite <- Heq; exact HT)) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite !ps2_req in Hd by lia. lia. }
split; [lia|]. split; [lia|].
split.
{ unfold in_app in Appa. destruct Appa as (_ & [H1 | (H1 & H2)]); [left; lia | right; lia]. }
intros x Hx. exact (blk_img tfibsegs B LAWS _ _ _ _ _ _ _ x HAR HinA ltac:(rewrite ps2_req by lia; lia)).
Qed.

(* ---- stage 2: from pstr_ret_facts at the return 0x85618 to parse_string_spec's fpostU at the `ret` ---- *)
Lemma pstr_stage2 : forall ly S U W regs mem md ch q ot text len p d (tb : list byte) tcap Q live peak cnt fail
    ly2 S2 W2 regs2 mem2 md2 a,
  fpreU tfibsegs B STK_parse_string ly S U W regs mem md ch -> FSupoisonU.fs_heads B ly S U ->
  YK11.getr regs 10 = w64 q ->
  PjIn.pj_in_ok tfibsegs (mrestrict (w_H W) mem) q text len p d tb ->
  rd_win tfibsegs regs ly W mem q ot ->
  rd_text tfibsegs B ly S W mem text len tcap ->
  p < text + len -> nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) ->
  plain_run tb text len p Q ->
  fs_glob tfibsegs W mem live peak cnt fail -> quiet cnt fail 1 ->
  Q + 1 + HEAD < MALLOC_MAX -> live + Q + 1 < 2 ^ 64 ->
  pstr_ret_facts B ly S U W regs mem md ot q p d Q text len tcap live peak cnt fail a tb ly2 S2 W2 regs2 mem2 md2 ->
  SRr tfibsegs W2 (YG0d.cfg_at tfibsegs RA_PSTR_MALLOC regs2 mem2 md2)
    (fpostU tfibsegs B (STK_parse_string + (ot - spZ regs)) ot FS_PSTAT_FP regs ly S U W mem md EV_fuzz_malloc
       (U ++ [(a - HEAD, HEAD)])
       (fun ly' S' W' regs' mem' md' =>
          YK11.getr regs' 10 = w64 a /\ 4096 + HEAD <= a /\
          ablocks B ly' S' = ablocks B ly S ++ [(a - HEAD, Q + 1 + HEAD)] /\
          fs_rblock tfibsegs B ly' S' W' mem' a (Q + 1) /\
          PjStruct.pj_cbytes tfibsegs (mrestrict (w_H W') mem') a (run_at tb text p Q) /\
          PjIn.pj_in_ok tfibsegs (mrestrict (w_H W') mem') q text len (p + Q + 2) d tb /\
          wkeep tfibsegs W W' mem mem' (spZ regs) ot q 24 /\
          rd_text tfibsegs B ly' S' W' mem' text len tcap /\
          fs_glob tfibsegs W' mem' (live + Q + 1) (Z.max peak (live + Q + 1)) (cnt + 1) fail)).
Proof.
intros ly S U W regs mem md ch q ot text len p d tb tcap Q live peak cnt fail ly2 S2 W2 regs2 mem2 md2 a
  HPRE FH H10 HIN HWIN HTX Hp Hq Hrun HGL0 Hquiet HQm Hlive HRF.
destruct HRF as (Rsp & R10 & R3 & R4 & R8 & R9 & R20 & R22 & R23 & R24 & RF & HJ & HARU & HFH & Ha16 & Ham & Hab & HRB &
  HIN2 & HTX2 & HWK & HGL).
pose proof HPRE as ((HAP & _ & _) & _).
pose proof HAP as (_ & Hra & _ & _ & _ & Hstk & _).
pose proof Hstk as (HSPal & _ & Hceil & HSTK & _ & H47 & _ & _ & Htophi).
pose proof HWIN as (Hq1 & Hq2 & _ & Hottop & _).
pose proof HTX as (_ & (HTX1 & _) & _).
pose proof HTX2 as (_ & (_ & _ & Htc & _) & _).
pose proof Hrun as (HQ0 & _).
pose proof HJ as (_ & Hly & _).
destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo2 & Hhi2 & _).
pose proof (ps2_blocks ly S ly2 S2 W2 _ md2 text tcap a Q (proj1 HARU) Hab HTX1 HQ0 Htc)
  as (Hnew & Hdisj & Hca & Hct & Happ & Himg).
exact (ps2_r0 ly S U W regs mem md ot q text len p d tb tcap Q live peak cnt fail a ly2 S2 W2 mem2 Hra HSPal Hceil HSTK
  ltac:(lia) H47 Hq1 Hq2 Hlo2 Hhi2 HIN2 HTX2 HTX1 Hrun Hab Ha16 Ham HRB HFH HWK HGL Hnew Hdisj Hca Hct Happ Himg
  regs2 md2 Rsp R10 R3 R4 R8 R9 R20 R22 R23 R24 RF HJ HARU).
Qed.
End W2.
