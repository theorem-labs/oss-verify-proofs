(* preset_base64_encode 0x84700 (preset_file.c:577-608) on fs.asan-ubsan (image B): the 3-byte loop's REGISTER LAYER
   and its INDUCTION (encR_loop), toward lib/B/FSH_Fn_writer.v's encode_spec. Same names and argument order as image A's
   loop block (lib/A/FSW_preset_base64_encode.v); every numeral and register here is B's.

   What it proves.
   - B's round state at the loop head 0x84788 (enc_rin / enc_rout / enc_gf / enc_conds / enc_alias / enc_sregs /
     enc_round_ss) and that a head state is one (enc_round_state, encR_round_state). B's round reads its input bytes
     through t4 = a7 + a5 (0x847c0 `add t4,a7,a5`; `lbu -3/-2/-1(t4)` at 0x847d4 / 0x847e8 / 0x8480c): the alias
     (a7 + a5 -> SOff 12 1) gives the engine t4 = a2 + 1, so A's input region on atom 12 (a2 = data + 3r + 2) serves.
     The second alias (s1 + a5 -> SOff 12 0) gives the next round's `add a2,s1,a5` (0x84784) as atom 12 + 3. B stores
     through t3 / t6 (both from t6 = x31: 0x8483c, 0x84884, 0x848c4, 0x84900), so the output region and its shent sit on
     atom 31. t0 / t1 / t2 are the literals 1, 2^64 - 1 - G_B64, 2^64 - 1 (0x84770, 0x84774, 0x84778). Three UBSan
     deciders the atom facts cannot decide are conditions of the state: 0x8478c `bltu a3,s1` (a3 = data + 3r), and
     0x84840 / 0x84888 `bltu t1,a3` on the second and third table index; the engine decides the other ten round
     deciders (0x84798, 0x8479c, 0x847b8, 0x847bc, 0x847f4, 0x847f8, 0x84848, 0x84890, 0x848c8, 0x848d0) from the
     literals and the atom facts. One engine run per segment (0x84788 -> 0x84800 -> 0x84850 -> 0x84898 -> 0x848d8 ->
     0x84910, seats 100 / 200 / 300 / 400 on x12) reaches the loop branch 0x84910 `bltu a5,s0` (BC_LTU (SOff 15 3)
     (SOff 8 0)) from enc_round_ss with no other stop (checked with vm_compute on the pinned fs.asan-ubsan table).
   - the shents of a round (enc_SH, enc_SH1 .. enc_SH4, enc_sh_ok, enc_sh_seat, encR_sh0, Ltac enc_shbase), the seats
     (encR_seat_dj, encR_seat_ok), the write bound (encR_wr_bound), the env the round reads (encR_round_env);
   - the loop's head and exit registers (encR_loop_regs at 0x84788, encR_exit_regs at 0x849b8: 0x849b0 `addi a1,t3,4`,
     0x849b4 `addi a3,a5,-2`, 0x849b8 `bgeu a3,s0,84b24`; x14 = G_B64 is kept because the tail reads a4 without
     reloading it, 0x84a28 / 0x84a38 / 0x84a80 / 0x84abc);
   - encR_loop: from the head of round r with the first r output quads written, all the rounds, by induction on a
     bound of len - 3r. Its one hypothesis RS is the round step (A's encR_round_step statement at B's head 0x84788 and
     exit 0x849b8), proved by the round-step lane.
   Boundaries and registers: the encB map (a working branch 187167cc7a6 encB-map.md, tables 2a-2c),
   rulings of a Theorem Labs lane 09:44Z (head 0x84788, encR_kept without 19 / 20, exit 0x849b8 with x14).

   rule 24: proves no function (kind: segment lemma of preset_base64_encode's walk - image-B loop-register layer + loop
   induction; the function's reuse search and CONFIRM: (internal path),
   a Theorem Labs lane 04:05:58Z)
   Ported from: lib/A/FSW_preset_base64_encode.v at a working branch 402eb5565fc lines 61-78 (enc_rin, enc_rout,
   enc_gf, enc_round_ss, enc_SH .. enc_SH4), 356-443 (enc_round_state), 462-494 (enc_sh_ok, enc_sh_seat), 1237 / 1241-1246
   (encR_extra3, encR_loop_regs), 1299-1366 (encR_round_state, encR_seat_dj), 1378-1437 (encR_wr_bound, encR_seat_ok,
   encR_round_env), 1463-1475 / 1491-1500 (encR_sh0, enc_shbase), 1510-1513 (encR_exit_regs); a working branch
   e1f485ea4e1 lines 2176-2228 (EncLoop: RS, encR_loop). Old-B donor a working branch b96980d72d1
   lib/B/Prog/preset_base64_encode_blocks.v:374-379 (BL: B's loop register file), :761-784 (enc_loop: the induction on
   len - 3k). *)
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
FSW_preset_base64_encode_W FSW_preset_base64_encode_R.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ---- the round's symbolic state at the loop head 0x84788 (atoms: 8 len, 9 data, 11 / 31 the output pointer q + 4r,
   12 the input pointer data + 3r + 2, 14 g_b64, 15 i = 3r + 2, 16 not data, 17 data + 1, 18 the shadow base, 36..38 the
   round's three input bytes; 100/200/300/400 the table seats a round's run adds). ---- *)
Definition enc_rin : YP09.region :=
  YP09.mkRegion (Some 12%nat) (-2) 1 0 0
    [YP09.mkChunk (-2) (CVal 1 (SOff 36 0)); YP09.mkChunk (-1) (CVal 1 (SOff 37 0));
     YP09.mkChunk 0 (CVal 1 (SOff 38 0))].
Definition enc_rout : YP09.region := YP09.mkRegion (Some 31%nat) 0 4 0 4 [].
Definition enc_gf : list (nat * afact) :=
  [(18%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (12%nat, mkAF 4096 PTOP 0); (31%nat, mkAF 4096 PTOP 0);
   (11%nat, mkAF 4096 PTOP 0); (8%nat, mkAF 0 (2 ^ 27) 0); (15%nat, mkAF 2 (2 ^ 27) 0);
   (14%nat, mkAF G_B64 G_B64 0); (9%nat, mkAF 4096 PTOP 0);
   (16%nat, mkAF (18446744073709551615 - PTOP) (18446744073709551615 - 4096) 0);
   (17%nat, mkAF 4097 (PTOP + 1) 0);
   (36%nat, mkAF 0 255 0); (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0)].
(* the second and third table index as the engine builds them (0x84828 .. 0x84838 and 0x84878 .. 0x84880) *)
Definition enc_ix1 : sv :=
  SAlu ALU_SRL (SAlu ALU_SLL
    (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SAlu ALU_SLL (SOff 36 0) (SLit 16))) (SLit 46)) (SLit 58).
Definition enc_ix2 : sv :=
  SAlu ALU_SRL (SAlu ALU_SLL (SAlu ALU_OR (SAlu ALU_SLL (SOff 37 0) (SLit 8)) (SOff 38 0)) (SLit 52)) (SLit 58).
(* the UBSan deciders the atom facts leave open: 0x8478c `bltu a3,s1` (a3 = data + 3r), 0x84840 and 0x84888
   `bltu t1,a3` (t1 = not g_b64, a3 the second / third index) *)
Definition enc_conds : list acond :=
  [mkAC BC_GEU (SOff 12 (-2)) (SOff 9 0); mkAC BC_GEU (SLit 18446744073709416351) enc_ix1;
   mkAC BC_GEU (SLit 18446744073709416351) enc_ix2].
(* 0x847c0 `add t4,a7,a5` = a2 + 1; 0x84784 `add a2,s1,a5` = a2 (+ 3 after the round's `addi a5,a5,3`) *)
Definition enc_alias : list (sv * sv) :=
  [(SAlu ALU_ADD (SOff 17 0) (SOff 15 0), SOff 12 1); (SAlu ALU_ADD (SOff 9 0) (SOff 15 0), SOff 12 0)].
(* t0 = snez data = 1, t1 = not g_b64, t2 = -1 as literals *)
Definition enc_sregs : list sv :=
  sr_set (sr_set (sr_set sr_atoms 5%bv (SLit 1)) 6%bv (SLit 18446744073709416351)) 7%bv
    (SLit 18446744073709551615).
Definition enc_round_ss (pc : Z) : sstate :=
  mkSS pc enc_sregs [enc_rin; enc_rout] None (mkFacts enc_gf enc_conds enc_alias).
(* the shents: the three input bytes at a2, the four output bytes reached through t6 and through a1, and one per
   table seat *)
Definition enc_SH : list shent := [mkSHE 12%nat (-2) 1; mkSHE 31%nat 0 4; mkSHE 11%nat 0 4].
Definition enc_SH1 : list shent := enc_SH ++ [mkSHE 100 0 1].
Definition enc_SH2 : list shent := enc_SH1 ++ [mkSHE 200 0 1].
Definition enc_SH3 : list shent := enc_SH2 ++ [mkSHE 300 0 1].
Definition enc_SH4 : list shent := enc_SH3 ++ [mkSHE 400 0 1].

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the shadow-cell pair (lib/B/FSH_Base.v FsShadowSyms) and the image facts (lib/B/FSH_Rt.v fs_img_facts), as in
   lib/B/FSW_preset_base64_encode_W.v's Section W *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis IMG : fs_img_facts tfibsegs B.

(* the head's register file: the atoms, with t0 / t1 / t2 as literals *)
Lemma enc_sregs_ok : forall (E : env) regs, regs_ok E sr_atoms regs ->
  getr regs 5 = w64 1 -> getr regs 6 = w64 18446744073709416351 -> getr regs 7 = w64 18446744073709551615 ->
  regs_ok E enc_sregs regs.
Proof.
intros E regs HR H5 H6 H7. apply regs_ok_by_cases. intros r Hr.
cbv [YP01.all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr];
  [ lazymatch goal with |- _ = sv_denot _ (sr_get enc_sregs ?x) =>
      let v := eval vm_compute in (sr_get enc_sregs x) in
      let w := eval vm_compute in (sr_get sr_atoms x) in
      change (sr_get enc_sregs x) with v;
      first [ cbn [sv_denot]; first [exact H5 | exact H6 | exact H7]
            | rewrite (HR x); change (sr_get sr_atoms x) with w; reflexivity ]
    end
  | ]).
destruct Hr.
Qed.

Lemma enc_round_state : forall (W : world tfibsegs) mem regs (E : env) out b0 b1 b2 d p len i pc,
  (* the env: atoms 0..31 are the registers, 36..38 the three input bytes *)
  regs_ok E sr_atoms regs ->
  ew E 36 = w64 b0 -> ew E 37 = w64 b1 -> ew E 38 = w64 b2 ->
  (* the registers the round reads *)
  getr regs 5 = w64 1 -> getr regs 6 = w64 18446744073709416351 -> getr regs 7 = w64 18446744073709551615 ->
  getr regs 8 = w64 len -> getr regs 9 = w64 d -> getr regs 11 = w64 out -> getr regs 12 = w64 p ->
  getr regs 14 = w64 G_B64 -> getr regs 15 = w64 i -> getr regs 16 = w64 (18446744073709551615 - d) ->
  getr regs 17 = w64 (d + 1) -> getr regs 18 = w64 SHADOW_OFF -> getr regs 31 = w64 out ->
  (* the input window and the output window *)
  val_mem tfibsegs (mrestrict (w_H W) mem) (p - 2) 1 b0 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) (p - 1) 1 b1 ->
  val_mem tfibsegs (mrestrict (w_H W) mem) p 1 b2 ->
  (forall o, 0 <= o < 4 -> writable_at tfibsegs (mrestrict (w_H W) mem) (out + o)) ->
  (* the numerals *)
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  p = d + i -> 4096 <= d -> p + 1 <= PTOP -> 4096 <= out -> out + 4 <= PTOP ->
  0 <= len <= 2 ^ 27 -> 2 <= i <= 2 ^ 27 ->
  (* the two heap windows are apart *)
  (p + 1 <= out \/ out + 4 <= p - 2) ->
  st_ok tfibsegs E (enc_round_ss pc)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 pc) mem (seg_rom tfibsegs))).
Proof.
intros W mem regs E out b0 b1 b2 d p len i pc HR E36 E37 E38
  R5 R6 R7 R8 R9 R11 R12 R14 R15 R16 R17 R18 R31 Vb0 Vb1 Vb2 HWout Hb0 Hb1 Hb2
  Hpdi Hd0 Hp1 Ho0 Ho1 Hlen Hi Hsep.
assert (EW : forall (r : bv 5) (n : nat), sr_get sr_atoms r = SOff n 0 -> ew E n = getr regs r).
{ intros r n Hn. rewrite (HR r), Hn, fsw_SOff0. reflexivity. }
assert (A8 : ew E 8 = w64 len) by (rewrite (EW 8%bv 8%nat ltac:(vm_compute; reflexivity)); exact R8).
assert (A9 : ew E 9 = w64 d) by (rewrite (EW 9%bv 9%nat ltac:(vm_compute; reflexivity)); exact R9).
assert (A11 : ew E 11 = w64 out) by (rewrite (EW 11%bv 11%nat ltac:(vm_compute; reflexivity)); exact R11).
assert (A12 : ew E 12 = w64 p) by (rewrite (EW 12%bv 12%nat ltac:(vm_compute; reflexivity)); exact R12).
assert (A14 : ew E 14 = w64 G_B64) by (rewrite (EW 14%bv 14%nat ltac:(vm_compute; reflexivity)); exact R14).
assert (A15 : ew E 15 = w64 i) by (rewrite (EW 15%bv 15%nat ltac:(vm_compute; reflexivity)); exact R15).
assert (A16 : ew E 16 = w64 (18446744073709551615 - d))
  by (rewrite (EW 16%bv 16%nat ltac:(vm_compute; reflexivity)); exact R16).
assert (A17 : ew E 17 = w64 (d + 1)) by (rewrite (EW 17%bv 17%nat ltac:(vm_compute; reflexivity)); exact R17).
assert (A18 : ew E 18 = w64 SHADOW_OFF) by (rewrite (EW 18%bv 18%nat ltac:(vm_compute; reflexivity)); exact R18).
assert (A31 : ew E 31 = w64 out) by (rewrite (EW 31%bv 31%nat ltac:(vm_compute; reflexivity)); exact R31).
assert (U8 : bv_unsigned (ew E 8) = len) by (rewrite A8; apply unsigned_lit_small; lia).
assert (U9 : bv_unsigned (ew E 9) = d) by (rewrite A9; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U11 : bv_unsigned (ew E 11) = out)
  by (rewrite A11; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U12 : bv_unsigned (ew E 12) = p)
  by (rewrite A12; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U14 : bv_unsigned (ew E 14) = G_B64)
  by (rewrite A14; apply unsigned_lit_small; unfold G_B64; lia).
assert (U15 : bv_unsigned (ew E 15) = i) by (rewrite A15; apply unsigned_lit_small; lia).
assert (U16 : bv_unsigned (ew E 16) = 18446744073709551615 - d)
  by (rewrite A16; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U17 : bv_unsigned (ew E 17) = d + 1)
  by (rewrite A17; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U18 : bv_unsigned (ew E 18) = SHADOW_OFF)
  by (rewrite A18; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U31 : bv_unsigned (ew E 31) = out)
  by (rewrite A31; apply unsigned_lit_small; unfold PTOP in *; lia).
assert (U36 : bv_unsigned (ew E 36) = b0) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U37 : bv_unsigned (ew E 37) = b1) by (rewrite E37; apply unsigned_lit_small; lia).
assert (U38 : bv_unsigned (ew E 38) = b2) by (rewrite E38; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. unfold enc_round_ss, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst
     ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact (enc_sregs_ok E regs HR R5 R6 R7)|].
split.
- split; [vm_compute; reflexivity|]. split.
  + constructor; [|constructor; [|constructor]].
    * (* the three input bytes *)
      unfold enc_rin, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U12. split; [lia|]. split; [unfold PTOP in *; lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor; [|constructor]]].
      -- apply (chunk_ok_val tfibsegs E _ p (-2) 1%N (SOff 36 0) b0);
          [rewrite fsw_SOff0, E36; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vb0].
      -- apply (chunk_ok_val tfibsegs E _ p (-1) 1%N (SOff 37 0) b1);
          [rewrite fsw_SOff0, E37; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vb1].
      -- apply (chunk_ok_val tfibsegs E _ p 0 1%N (SOff 38 0) b2);
          [rewrite fsw_SOff0, E38; reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
          | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_r; exact Vb2].
    * (* the output window *)
      unfold enc_rout, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U31. split; [lia|]. split; [unfold PTOP in *; lia|].
      split; [intros o Ho; apply HWout; lia|]. constructor.
  + (* the two regions are apart *)
    apply pairwise_disjoint_of_extents.
    unfold enc_rin, enc_rout, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U12, U31.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold PTOP in *.
    repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
- split; [|split].
  + (* the atom facts *)
    unfold enc_gf. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U18, U12, U31, U11, U8, U15, U14, U9, U16, U17, U36, U37, U38.
    rewrite !Z.pow_0_r.
    unfold PTOP, G_B64, SHADOW_OFF in *.
    repeat split; try lia; try (apply Z.mod_1_r).
  + (* the three conditions *)
    cbn [f_conds]. unfold enc_conds. cbn [conds_ok]. unfold acond_ok. cbn [ac_c ac_a ac_b].
    split; [|split; [|split; [|exact I]]].
    * rewrite branch_geu_U, (U_atom_off E 12 p (-2) A12 ltac:(unfold PTOP in *; lia) ltac:(unfold PTOP in *; lia)),
        (U_atom E 9 d A9 ltac:(unfold PTOP in *; lia)).
      apply negb_true_iff, Z.ltb_ge. lia.
    * unfold enc_ix1. rewrite branch_geu_U, U_SLit, (enc_U_t1 E 36 37 b0 b1 E36 E37 Hb0 Hb1).
      rewrite zcanon_id by (unfold M64; lia).
      apply negb_true_iff, Z.ltb_ge. lia.
    * unfold enc_ix2. rewrite branch_geu_U, U_SLit, (enc_U_t2 E 37 38 b1 b2 E37 E38 Hb1 Hb2).
      rewrite zcanon_id by (unfold M64; lia).
      apply negb_true_iff, Z.ltb_ge. lia.
  + (* the two aliases *)
    cbn [f_alias]. unfold enc_alias. cbn [alias_ok].
    split; [|split; [|exact I]].
    * apply U_inj.
      rewrite (enc_U_add2 E 17 15 0 0 (d + 1) i A17 A15), (U_atom_off E 12 p 1 A12);
        unfold PTOP in *; lia.
    * apply U_inj.
      rewrite (enc_U_add2 E 9 15 0 0 d i A9 A15), (U_atom E 12 p A12); unfold PTOP in *; lia.
Qed.

Lemma enc_sh_ok : forall (W : world tfibsegs) mem (E : env) p out,
  U E enc_Bx = SHADOW_OFF -> U E (SOff 12 0) = p -> U E (SOff 31 0) = out -> U E (SOff 11 0) = out ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (p - 2) 3 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF out 4 ->
  enc_apart (p - 2) (p + 1) -> enc_apart out (out + 4) ->
  sh_ok tfibsegs enc_Bx enc_SH E (mrestrict (w_H W) mem).
Proof.
intros W mem E p out HB H12 H31 H11 HRAin HRAout Hp Ho.
unfold sh_ok, enc_SH. constructor; [|constructor; [|constructor; [|constructor]]].
- apply (enc_she W mem E 12%nat p (-2) 1 (p - 2) 3 HB H12 HRAin); [lia | lia | lia|].
  intros x Hx. apply Hp. lia.
- apply (enc_she W mem E 31%nat out 0 4 out 4 HB H31 HRAout); [lia | lia | lia|].
  intros x Hx. apply Ho. lia.
- apply (enc_she W mem E 11%nat out 0 4 out 4 HB H11 HRAout); [lia | lia | lia|].
  intros x Hx. apply Ho. lia.
Qed.

Lemma enc_sh_seat : forall (W : world tfibsegs) mem (E : env) p out (n : nat) v,
  U E enc_Bx = SHADOW_OFF -> U E (SOff 12 0) = p -> U E (SOff 31 0) = out -> U E (SOff 11 0) = out ->
  U E (SOff n 0) = G_B64 + v -> 0 <= v < 64 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (p - 2) 3 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF out 4 ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF G_B64 65 ->
  enc_apart (p - 2) (p + 1) -> enc_apart out (out + 4) ->
  sh_ok tfibsegs enc_Bx (enc_SH ++ [mkSHE n 0 1]) E (mrestrict (w_H W) mem).
Proof.
intros W mem E p out n v HB H12 H31 H11 Hn Hv HRAin HRAout HRAt Hp Ho.
unfold sh_ok. apply Forall_app. split.
- exact (enc_sh_ok W mem E p out HB H12 H31 H11 HRAin HRAout Hp Ho).
- constructor; [|constructor].
  apply (enc_she W mem E n (G_B64 + v) 0 1 G_B64 65 HB Hn HRAt); [lia | lia | lia|].
  intros x Hx. unfold G_B64, SHADOW_OFF in *. lia.
Qed.

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
(* the entry frame: ra, s0, s1, s2, s3, s4 saved by the prologue (0x84704 .. 0x84718: sd ra,40(sp) .. sd s4,0(sp) after
   addi sp,sp,-48), still there after the call *)
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

(* lib/B/FSW_preset_base64_encode_R.v's Section R at this section's variables. After its `End R. End W.` each of its
   definitions and lemmas takes the section variables and hypotheses it uses (their order: About in the build); each
   local copy below applies it to them, so the text below is A's, where the loop block sits inside Section R. The
   definitions are Lets; the lemmas are Local Lemmas (not Lets: a Prop-typed Let sits in every proof's context, where
   lia would read it and the lemma would take its section variables), so Import of this file keeps R's names. *)
Let encR_out := FSW_preset_base64_encode_R.encR_out len q.
Let encR_agree := FSW_preset_base64_encode_R.encR_agree memc len q.
Let encR_inv := FSW_preset_base64_encode_R.encR_inv B ly0 St0 U0 W0 mem0 md0 regs0 lyc Sc Wc memc len q.
Let encR_kept := FSW_preset_base64_encode_R.encR_kept regs0.
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
Local Lemma encR_in_byte : forall mem (j : nat), encR_agree mem -> (j < length bs)%nat ->
  val_mem tfibsegs (mrestrict (w_H Wc) mem) (data + Z.of_nat j) 1 (nth j bs 0) /\ 0 <= nth j bs 0 < 256.
Proof.
exact (FSW_preset_base64_encode_R.encR_in_byte B ly0 St0 U0 regs0 lyc Sc Wc memc mdc
  data len q live peak cnt kd bs HLN HBSL HDLO HDHI HARUc HAB HDB HDATc).
Qed.
Local Lemma encR_dj : 0 < len -> data + len <= q \/ q + enc_size len <= data.
Proof.
exact (FSW_preset_base64_encode_R.encR_dj B ly0 St0 U0 regs0 lyc Sc Wc memc mdc
  data len q live peak cnt kd bs HLN HBSL HARUc HAB HDB).
Qed.
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

(* ---- the 3-byte loop (0x84788 .. 0x84910). At the head of round r (0x84788, after the back-edge target's
   `add a2,s1,a5` 0x84784): a1 = t6 = q + 4r (the four output bytes of this round), a2 = data + 3r + 2 (the third input
   byte), a5 = 3r + 2, a4 = g_b64, s0 = len, s1 = data, a0 = q, a6 = not data, a7 = data + 1, t0 = 1, t1 = not g_b64,
   t2 = -1 (0x84764 .. 0x84780). The three input bytes of the round are bs[3r], bs[3r+1], bs[3r+2]. ---- *)
Definition encR_extra3 (b0 b1 b2 : Z) : list word := [w64 0; w64 0; w64 0; w64 0; w64 b0; w64 b1; w64 b2].
Definition encR_loop_regs (ms : machine_state) (r : Z) : Prop :=
  getr (ms_regs ms) 5 = w64 1 /\ getr (ms_regs ms) 6 = w64 18446744073709416351 /\
  getr (ms_regs ms) 7 = w64 18446744073709551615 /\
  getr (ms_regs ms) 8 = w64 len /\ getr (ms_regs ms) 9 = w64 data /\ getr (ms_regs ms) 10 = w64 q /\
  getr (ms_regs ms) 11 = w64 (q + 4 * r) /\ getr (ms_regs ms) 12 = w64 (data + 3 * r + 2) /\
  getr (ms_regs ms) 14 = w64 G_B64 /\ getr (ms_regs ms) 15 = w64 (3 * r + 2) /\
  getr (ms_regs ms) 16 = w64 (18446744073709551615 - data) /\ getr (ms_regs ms) 17 = w64 (data + 1) /\
  getr (ms_regs ms) 18 = w64 SHADOW_OFF /\ getr (ms_regs ms) 31 = w64 (q + 4 * r) /\
  spZ (ms_regs ms) = spZ regs0 - 48 /\ encR_kept ms.

(* the registers at the loop's exit (0x849b8), after R = r + 1 rounds: a1 = t3 + 4 (0x849b0), a3 = a5 - 2 (0x849b4),
   a4 = g_b64 (read by the tail) *)
Definition encR_exit_regs (ms : machine_state) (R : Z) : Prop :=
  getr (ms_regs ms) 8 = w64 len /\ getr (ms_regs ms) 9 = w64 data /\ getr (ms_regs ms) 10 = w64 q /\
  getr (ms_regs ms) 11 = w64 (q + 4 * R) /\ getr (ms_regs ms) 13 = w64 (3 * R) /\
  getr (ms_regs ms) 14 = w64 G_B64 /\
  getr (ms_regs ms) 18 = w64 SHADOW_OFF /\ spZ (ms_regs ms) = spZ regs0 - 48 /\ encR_kept ms.

Lemma encR_round_state : forall ms md r b0 b1 b2,
  0 <= r -> 3 * r + 3 <= len ->
  encR_inv (ms_mem ms) md -> encR_loop_regs ms r ->
  nth (Z.to_nat (3 * r)) bs 0 = b0 -> nth (Z.to_nat (3 * r + 1)) bs 0 = b1 ->
  nth (Z.to_nat (3 * r + 2)) bs 0 = b2 ->
  st_ok tfibsegs (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (enc_round_ss 0x84788)
    (restrict (w_H Wc) (mkst (ms_regs ms) (w64 0x84788) (ms_mem ms) (seg_rom tfibsegs)))
  /\ 0 <= b0 < 256 /\ 0 <= b1 < 256 /\ 0 <= b2 < 256.
Proof.
intros ms md r b0 b1 b2 Hr Hr3 (HJ & HARU & HA) HR N0 N1 N2.
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
pose proof HR as (R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R14 & R15 & R16 & R17 & R18 & R31 & Rsp & Rk).
assert (HBL : Z.of_nat (length bs) = len) by exact HBSL.
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * r)) HA ltac:(lia)) as (V0 & B0).
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * r + 1)) HA ltac:(lia)) as (V1 & B1).
destruct (encR_in_byte (ms_mem ms) (Z.to_nat (3 * r + 2)) HA ltac:(lia)) as (V2 & B2).
rewrite N0 in V0, B0. rewrite N1 in V1, B1. rewrite N2 in V2, B2.
assert (Hd0 : data + Z.of_nat (Z.to_nat (3 * r)) = data + 3 * r + 2 - 2) by lia.
assert (Hd1 : data + Z.of_nat (Z.to_nat (3 * r + 1)) = data + 3 * r + 2 - 1) by lia.
assert (Hd2 : data + Z.of_nat (Z.to_nat (3 * r + 2)) = data + 3 * r + 2) by lia.
rewrite Hd0 in V0. rewrite Hd1 in V1. rewrite Hd2 in V2.
split; [|split; [exact B0 | split; [exact B1 | exact B2]]].
apply (enc_round_state Wc (ms_mem ms) (ms_regs ms) (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2))
  (q + 4 * r) b0 b1 b2 data (data + 3 * r + 2) len (3 * r + 2) 0x84788).
- apply regs_ok_Ereg.
- change 36%nat with (32 + 4)%nat. rewrite ew_Ereg_extra. reflexivity.
- change 37%nat with (32 + 5)%nat. rewrite ew_Ereg_extra. reflexivity.
- change 38%nat with (32 + 6)%nat. rewrite ew_Ereg_extra. reflexivity.
- exact R5.
- exact R6.
- exact R7.
- exact R8.
- exact R9.
- exact R11.
- exact R12.
- exact R14.
- exact R15.
- exact R16.
- exact R17.
- exact R18.
- exact R31.
- exact V0.
- exact V1.
- exact V2.
- intros o Ho. replace (q + 4 * r + o) with (q + (4 * r + o)) by lia.
  apply (encR_wr_out (ms_mem ms) md HARU). unfold enc_size in *. lia.
- exact B0.
- exact B1.
- exact B2.
- lia.
- exact HDLO.
- unfold PTOP. lia.
- unfold HEAD in *. lia.
- unfold PTOP, enc_size in *. lia.
- lia.
- lia.
- destruct (encR_dj ltac:(lia)) as [H|H]; [left | right]; unfold enc_size in *; lia.
Qed.

(* a table seat is apart from the round's two windows *)
Lemma encR_seat_dj : forall (E : env) (n : nat) (av r : Z) (cs : list YP09.chunk),
  bv_unsigned (ew E n) = av -> bv_unsigned (ew E 12) = data + 3 * r + 2 ->
  bv_unsigned (ew E 31) = q + 4 * r -> G_B64 <= av < G_B64 + 64 -> 0 <= r -> 3 * r + 3 <= len ->
  all_disjoint E (YP09.mkRegion (Some n) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff (S n) 0))])
    [enc_rin; YP09.mkRegion (Some 31%nat) 0 4 0 4 cs].
Proof.
intros E n av r cs Hn H12 H31 Hav Hr Hr3.
pose proof encR_size_pos as HM.
apply all_disjoint_of_extents. unfold enc_rin, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hn, H12, H31.
cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
destruct (encR_dj_in_tab ltac:(lia)) as [D1|D1]; destruct encR_dj_out_tab as [D2|D2];
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold G_B64, enc_size in *; lia.
Qed.

(* every byte a round's run may write is an output byte: the only region with a write window is the output
   quad, based on atom 31 *)
Lemma encR_wr_bound : forall (E : env) (rs : list YP09.region) a r,
  Forall (fun rg => YP09.r_whi rg <= YP09.r_wlo rg \/
            (YP09.r_base rg = Some 31%nat /\ YP09.r_wlo rg = 0 /\ YP09.r_whi rg = 4)) rs ->
  bv_unsigned (ew E 31) = q + 4 * r -> 0 <= r -> 3 * r + 3 <= len ->
  in_wrange E rs a -> encR_out a.
Proof.
intros E rs a r HF H31 Hr Hr3 (rg & Hin & Hrg).
pose proof encR_size_pos as HM.
destruct (proj1 (Forall_forall _ _) HF rg Hin) as [Hro | (Hb & Hl & Hh)]; [lia|].
rewrite Hb, Hl, Hh in Hrg. cbn [base_val] in Hrg. rewrite H31 in Hrg.
unfold encR_out, FSW_preset_base64_encode_R.encR_out, enc_size in *. lia.
Qed.

(* one table seat: the register holds g_b64 + v, the byte there is the table's, and the one-byte region is
   apart from the round's two windows *)
Lemma encR_seat_ok : forall (msX : machine_state) (E : env) ss (rg : bv 5) (n : nat) v r mdx cs,
  encR_agree (ms_mem msX) -> ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc (ms_mem msX) mdx ->
  0 <= r -> 3 * r + 3 <= len -> 0 <= v < 64 ->
  st_ok tfibsegs E ss (restrict (w_H Wc) msX) -> ss_atoms_lt n ss = true -> rg <> 0%bv -> (31 < n)%nat ->
  getr (ms_regs msX) rg = w64 (G_B64 + v) ->
  bv_unsigned (ew E 12) = data + 3 * r + 2 -> bv_unsigned (ew E 31) = q + 4 * r ->
  ss_mem ss = [enc_rin; YP09.mkRegion (Some 31%nat) 0 4 0 4 cs] ->
  st_ok tfibsegs (ewset (ewset E n (w64 (G_B64 + v))) (S n) (w64 (WriterSpec.b64c v)))
    (enc_seat ss rg n G_B64 (G_B64 + 63)) (restrict (w_H Wc) msX).
Proof.
intros msX E ss rg n v r mdx cs HA HARU Hr Hr3 Hv HS Hat Hrg Hn31 Hreg H12 H31 Hmem.
pose proof (b64c_range v Hv) as HB.
apply (enc_seat_ro1 E ss (restrict (w_H Wc) msX) rg n (G_B64 + v) (WriterSpec.b64c v) G_B64 (G_B64 + 63)
  HS Hat Hrg).
- cbn [ms_regs restrict]. exact Hreg.
- unfold G_B64. lia.
- lia.
- unfold G_B64. lia.
- exact HB.
- cbn [ms_mem restrict].
  exact (encR_tab_keep (ms_mem msX) HA HTABc v Hv).
- rewrite Hmem.
  apply (encR_seat_dj _ n (G_B64 + v) r cs).
  + rewrite ew_ewset_other by lia. rewrite ew_ewset_same. apply unsigned_lit_small. unfold G_B64. lia.
  + rewrite !ew_ewset_other by lia. exact H12.
  + rewrite !ew_ewset_other by lia. exact H31.
  + unfold G_B64. lia.
  + lia.
  + lia.
Qed.

(* the round's registers at the loop head, as the walk's env reads them *)
Lemma encR_round_env : forall ms r b0 b1 b2, encR_loop_regs ms r ->
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 9 = w64 data /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 11 = w64 (q + 4 * r) /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 12 = w64 (data + 3 * r + 2) /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 14 = w64 G_B64 /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 15 = w64 (3 * r + 2) /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 18 = w64 SHADOW_OFF /\
  ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 31 = w64 (q + 4 * r).
Proof.
intros ms r b0 b1 b2 (R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R14 & R15 & R16 & R17 & R18 & R31 & Rsp & Rk).
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 9 9%bv eq_refl); exact R9|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 11 11%bv eq_refl); exact R11|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 12 12%bv eq_refl); exact R12|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 14 14%bv eq_refl); exact R14|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 15 15%bv eq_refl); exact R15|].
split; [rewrite (ew_Ereg_nat (ms_regs ms) _ 18 18%bv eq_refl); exact R18|].
rewrite (ew_Ereg_nat (ms_regs ms) _ 31 31%bv eq_refl); exact R31.
Qed.

(* the round's shent list, at any invariant memory and any env that reads the round's registers *)
Lemma encR_sh0 : forall mem (mdx : Model) (E : env) r, encR_agree mem -> 0 <= r -> 3 * r + 3 <= len ->
  ARU tfibsegs B lyc Sc (U0 ++ [(q - HEAD, HEAD)]) Wc mem mdx ->
  U E enc_Bx = SHADOW_OFF -> U E (SOff 12 0) = data + 3 * r + 2 -> U E (SOff 31 0) = q + 4 * r ->
  U E (SOff 11 0) = q + 4 * r ->
  sh_ok tfibsegs enc_Bx enc_SH E (mrestrict (w_H Wc) mem).
Proof.
intros mem mdx E r HA Hr Hr3 HARU HB H12 H31 H11. pose proof encR_size_pos as HM.
apply (enc_sh_ok Wc mem E (data + 3 * r + 2) (q + 4 * r) HB H12 H31 H11).
- intros x Hx. apply (encR_ra_in mem mdx HARU ltac:(lia)). lia.
- intros x Hx. apply (encR_ra_out mem mdx HARU). unfold enc_size in *. lia.
- intros x Hx. apply (encR_in_apart ltac:(lia)). lia.
- intros x Hx. apply (proj1 encR_out_facts). unfold enc_size in *. lia.
Qed.

(* the round's shent list at a state whose env reads the round's registers (A11 / A12 / A31 / A18 in context) *)
Ltac enc_shbase memx HAx rr HrA HrB HARUx A11x A12x A31x A18x :=
  apply (encR_sh0 memx _ _ rr HAx HrA HrB HARUx); apply FSW_preset_base64_encode_R.encR_U_of_bv;
  first [ solve [repeat (rewrite ew_ewset_other by lia); rewrite A18x; apply unsigned_lit_small;
                 unfold SHADOW_OFF; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A12x; apply unsigned_lit_small; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A31x; apply unsigned_lit_small;
                 unfold enc_size in *; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A11x; apply unsigned_lit_small;
                 unfold enc_size in *; lia]
        | solve [unfold SHADOW_OFF; lia] | solve [unfold enc_size in *; lia] | solve [lia] ].

(* ==== BEGIN EncLoop (a Theorem Labs lane) ==== *)
(* ---- the 3-byte loop, all its rounds: from the head of round r (0x84788), with the first r output quads
   written, each round is one round step (KNEXT is the head of round r + 1, KEXIT the loop's exit at 0x849b8 after
   R = r + 1 rounds, where 3R <= len <= 3R + 2), by induction on len - 3r. RS is the round step's statement (A's
   encR_round_step at B's head and exit), held as a hypothesis: the round-step lane proves it. ---- *)
Section EncLoop.
Hypothesis RS : forall ms md r b0 b1 b2 (Q : world tfibsegs -> config -> Prop),
  0 <= r -> 3 * r + 3 <= len ->
  encR_inv (ms_mem ms) md -> encR_loop_regs ms r ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs)) ->
  nth (Z.to_nat (3 * r)) bs 0 = b0 -> nth (Z.to_nat (3 * r + 1)) bs 0 = b1 ->
  nth (Z.to_nat (3 * r + 2)) bs 0 = b2 ->
  (forall ms' md', 3 * (r + 1) + 3 <= len -> encR_inv (ms_mem ms') md' -> encR_loop_regs ms' (r + 1) ->
     ms' = mkst (ms_regs ms') (w64 0x84788) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  (forall ms' md', len <= 3 * (r + 1) + 2 -> encR_inv (ms_mem ms') md' -> encR_exit_regs ms' (r + 1) ->
     ms' = mkst (ms_regs ms') (w64 0x849b8) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg (mkst (ms_regs ms) (w64 0x84788) (ms_mem ms) (seg_rom tfibsegs)) md) Q.

Lemma encR_loop : forall ms md r (Q : world tfibsegs -> config -> Prop),
  0 <= r -> 3 * r + 3 <= len ->
  encR_inv (ms_mem ms) md -> encR_loop_regs ms r ->
  garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) q
    (WriterSpec.b64_enc (firstn (Z.to_nat (3 * r)) bs)) ->
  (forall ms' md' R, len <= 3 * R + 2 -> 3 * R <= len ->
     encR_inv (ms_mem ms') md' -> encR_exit_regs ms' R ->
     ms' = mkst (ms_regs ms') (w64 0x849b8) (ms_mem ms') (seg_rom tfibsegs) ->
     garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms')) q
       (WriterSpec.b64_enc (firstn (Z.to_nat (3 * R)) bs)) ->
     SRr tfibsegs Wc (mkCfg ms' md') Q) ->
  SRr tfibsegs Wc (mkCfg (mkst (ms_regs ms) (w64 0x84788) (ms_mem ms) (seg_rom tfibsegs)) md) Q.
Proof.
intros ms md r Q Hr Hr3.
assert (Hn : exists n, (Z.to_nat (len - 3 * r) <= n)%nat) by (exists (Z.to_nat (len - 3 * r)); lia).
destruct Hn as (n & Hn). revert ms md r Hr Hr3 Hn.
induction n as [|n IH]; intros ms md r Hr Hr3 Hn HINV HR HPRE KEXIT; [lia|].
apply (RS ms md r (nth (Z.to_nat (3 * r)) bs 0) (nth (Z.to_nat (3 * r + 1)) bs 0)
  (nth (Z.to_nat (3 * r + 2)) bs 0) Q Hr Hr3 HINV HR HPRE eq_refl eq_refl eq_refl).
- intros ms' md' Hr3' HINV' HR' HPC HPRE'. rewrite HPC.
  exact (IH ms' md' (r + 1) ltac:(lia) Hr3' ltac:(lia) HINV' HR' HPRE' KEXIT).
- intros ms' md' Hx HINV' HX HPC HPRE'.
  exact (KEXIT ms' md' (r + 1) Hx ltac:(lia) HINV' HX HPC HPRE').
Qed.
End EncLoop.
About encR_loop.
Print Assumptions encR_loop.
(* ==== END EncLoop (a Theorem Labs lane) ==== *)
End R.

End W.
Print Assumptions enc_round_state.
Print Assumptions encR_round_state.
Print Assumptions encR_seat_ok.
Print Assumptions encR_sh0.
Print Assumptions encR_wr_bound.
Print Assumptions encR_round_env.
