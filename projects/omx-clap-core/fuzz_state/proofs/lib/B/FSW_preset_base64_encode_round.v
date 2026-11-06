(* preset_base64_encode 0x84700 (preset_file.c:577-608) on fs.asan-ubsan (image B): ONE ROUND of the 3-byte loop,
   encR_round_step, proved toward lib/B/FSH_Fn_writer.v's encode_spec. The statement is image A's encR_round_step
   (lib/A/FSW_preset_base64_encode.v) with the loop head 0x843fc -> 0x84788 and the loop exit 0x845dc -> 0x849b8, over
   the loop-register layer's encR_loop_regs / encR_exit_regs (lib/B/FSW_preset_base64_encode_loop.v); it is the one
   hypothesis of that file's loop induction encR_loop.

   What it proves: from the loop head 0x84788 of round r (s0 = len, s1 = data, a0 = q, a1 = t6 = q + 4r,
   a2 = data + 3r + 2, a5 = 3r + 2, a4 = g_b64, a6 = ~data, a7 = data + 1, t0 = 1, t1 = ~g_b64, t2 = -1, s2 = the shadow
   offset), the round 0x84788 .. 0x84910 reads the three input bytes bs[3r], bs[3r+1], bs[3r+2], looks up the four
   table letters and stores them at q + 4r .. q + 4r + 3, writing nothing else; then the branch `bltu a5,s0` at 0x84910
   either goes round again (0x84784 `add a2,s1,a5`, back at the head 0x84788 with the registers of round r + 1: KNEXT)
   or leaves the loop (0x84914 `j 0x849b0`, `addi a1,t3,4`, `addi a3,a5,-2`, at 0x849b8 with a1 = q + 4(r + 1),
   a3 = 3(r + 1): KEXIT). The base64 text written so far gains the round's four letters (encR_prefix_step).
   The round is cut, as A's, into five token runs at the four table reads: 0x84788 -> 0x84800 (the three input checks,
   the first index, seat 100 on a2), -> 0x84850 (letter 0, seat 200), -> 0x84898 (letter 1, seat 300), -> 0x848d8
   (letter 2, seat 400), -> 0x84910 (letter 3 and the counters).

   Deciders refuted here.
   - UBSan (branch to the `unimp` at 0x84b58), the 13 of the round, each decided not taken by the token engine from the
     round state enc_round_ss (lib/B/FSW_preset_base64_encode_loop.v, whose encR_round_state proves its facts and
     conditions; the same arithmetic as lib/B/FSW_preset_base64_encode_ub.v's enc_ub_<addr>, named per decider below).
     By the state's three conditions enc_conds:
     0x8478c `bltu a3,s1` (BC_GEU (SOff 12 (-2)) (SOff 9 0); enc_ub_8478c), 0x84840 and 0x84888 `bltu t1,a3`
     (BC_GEU (SLit (2^64-1-g_b64)) enc_ix1 / enc_ix2; enc_ub_84840 / enc_ub_84888). By the literals and the atom facts:
     0x84798 `beqz t4` by t0 = SLit 1 and data + 3r >= 4094 (enc_ub_84798); 0x8479c `beqz s1` by atom 9 in
     [4096, PTOP] (enc_ub_8479c); 0x847b8 / 0x847bc `bltu a6,a3` / `bltu a6,a5` by atom 16 = ~data in
     [2^64-1-PTOP, 2^64-4097] against 3r + 1 / 3r + 2 <= 2^27 (enc_ub_847b8 / enc_ub_847bc); 0x847f4 / 0x848c8
     `bltu t1,idx` by t1 = SLit (2^64-1-g_b64) against b0 >> 2 / b2 & 63 (enc_ub_847f4 / enc_ub_848c8); 0x847f8 /
     0x84848 / 0x84890 / 0x848d0 `beq t3|t6,t2` by atom 31 = q + 4r in [4096, PTOP] against t2 = SLit (2^64-1)
     (enc_ub_847f8 / enc_ub_84848 / enc_ub_84890 / enc_ub_848d0). Each token run below reaches its stop pc
     TS_running, so no branch to 0x84b58 is taken.
   - ASan (report-sites-B.tsv rows 140, 152-161: the 11 inline checks of the round, main-path `bnez` 0x847b0 0x847d8
     0x847ec 0x84810 0x84824 0x8485c 0x84874 0x848a4 0x848bc 0x848e4 0x848fc): BY CONSTRUCTION, as A's rows 115,
     126-135 (HANDOFF2.md:41-44): the shents enc_SH (the input bytes data + 3r .. data + 3r + 2 on atom 12, the output
     bytes q + 4r .. q + 4r + 3 on atoms 31 and 11) and the seats 100 / 200 / 300 / 400 make every shadow byte the
     token run reads addressable (encR_sh0, encR_shent_seat), so each run stops TS_running with no obligation and no
     slow path or __asan_report_* edge is taken.

   rule 24: proves function preset_base64_encode (part round; reuse search: proof-index preset_base64_encode,
   ported from a working branch 402eb5565fc + donor a working branch b96980d72d1)
   Ported from: lib/A/FSW_preset_base64_encode.v (a working branch 402eb5565fc, encR_round_step lines 1571-2009
   with the branch and the two hand-offs as a Theorem Labs lane's worktree text of 09:52Z, lines 1571-2229 there, and encR_kept_reg
   1571-1580 there); image-B step order and UBSan / ASan deciders from the old-B donor a working branch
   b96980d72d1 lib/B/Prog/preset_base64_encode_blocks.v:374-379 (BL, the loop's register file), 401-456 (enc_B_r1 /
   enc_B_r2: 0x84784 -> 0x84814), 470-633 (enc_B_o0 .. enc_B_o3: 0x84814 -> 0x84910), 658-784 (enc_iter / enc_loop:
   the branch `bltu a5,s0` at 0x84910 and the exit 0x84914). *)
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
FSW_preset_base64_encode_W FSW_preset_base64_encode_R FSW_preset_base64_encode_loop.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
From Ltac2 Require Ltac2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* The W / R / loop files close their sections, so each of their constants takes the section variables (and the
   section hypotheses) it uses. encI applies a constant to exactly those, by the names of its leading binders, from
   this file's sections below (which repeat the R file's variables and hypotheses under the same names). *)
Module EncRI.
Import Ltac2.
Ltac2 secv () : ident list :=
  [@fx; @rc; @SK; @B; @HSS; @IMG; @ly0; @St0; @U0; @W0; @mem0; @md0; @regs0; @lyc; @Sc; @Wc; @memc; @mdc;
   @data; @len; @q; @live; @peak; @cnt; @fail; @kd; @bs; @HLN; @HBS; @HBSL; @HDLO; @HDHI; @HARUc; @HHEADS;
   @HQB; @HAB; @HQ16; @HDB; @HRBc; @HGLOBc; @HTABc; @HRATc; @HDATc; @HKEEPc; @HFRAMEc; @HSP0; @HRA0].
Ltac2 rec inst (t : constr) : constr :=
  match Constr.Unsafe.kind (Constr.type t) with
  | Constr.Unsafe.Prod b _ =>
      match Constr.Binder.name b with
      | Some id =>
          if List.exist (Ident.equal id) (secv ()) then
            inst (Constr.Unsafe.make (Constr.Unsafe.App t [| Control.hyp id |]))
          else t
      | None => t
      end
  | _ => t
  end.
Ltac2 go (x : Ltac1.t) : unit := let t := Option.get (Ltac1.to_constr x) in let r := inst t in exact $r.
End EncRI.
Ltac encI X := let f := ltac2:(x |- EncRI.go x) in f X.
Set Default Proof Mode "Classic".

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
(* what the call's entry memory holds (the fuzz_malloc call's post, read at memc) *)
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

(* the W / R / loop constants at this section's variables *)
Local Notation encR_inv := (ltac:(encI (@FSW_preset_base64_encode_R.encR_inv))) (only parsing).
Local Notation encR_agree := (ltac:(encI (@FSW_preset_base64_encode_R.encR_agree))) (only parsing).
Local Notation encR_out := (ltac:(encI (@FSW_preset_base64_encode_R.encR_out))) (only parsing).
Local Notation encR_size_pos := (ltac:(encI (@FSW_preset_base64_encode_R.encR_size_pos))) (only parsing).
Local Notation encR_out_facts := (ltac:(encI (@FSW_preset_base64_encode_R.encR_out_facts))) (only parsing).
Local Notation encR_new_block := (ltac:(encI (@FSW_preset_base64_encode_R.encR_new_block))) (only parsing).
Local Notation encR_shent_seat := (ltac:(encI (@FSW_preset_base64_encode_R.encR_shent_seat))) (only parsing).
Local Notation encR_U_of_bv := (ltac:(encI (@FSW_preset_base64_encode_R.encR_U_of_bv))) (only parsing).
Local Notation encR_prefix_step := (ltac:(encI (@FSW_preset_base64_encode_R.encR_prefix_step))) (only parsing).
Local Notation encR_garr8_app4 := (ltac:(encI (@FSW_preset_base64_encode_R.encR_garr8_app4))) (only parsing).
Local Notation encR_garr8_keep := (ltac:(encI (@FSW_preset_base64_encode_R.encR_garr8_keep))) (only parsing).
Local Notation enc_frame_X := (ltac:(encI (@FSW_preset_base64_encode_W.enc_frame_X))) (only parsing).
Local Notation encR_loop_regs := (ltac:(encI (@FSW_preset_base64_encode_loop.encR_loop_regs))) (only parsing).
Local Notation encR_exit_regs := (ltac:(encI (@FSW_preset_base64_encode_loop.encR_exit_regs))) (only parsing).
Local Notation encR_round_state := (ltac:(encI (@FSW_preset_base64_encode_loop.encR_round_state))) (only parsing).
Local Notation encR_round_env := (ltac:(encI (@FSW_preset_base64_encode_loop.encR_round_env))) (only parsing).
Local Notation encR_seat_ok := (ltac:(encI (@FSW_preset_base64_encode_loop.encR_seat_ok))) (only parsing).
Local Notation encR_sh0 := (ltac:(encI (@FSW_preset_base64_encode_loop.encR_sh0))) (only parsing).

(* a callee-saved register the round never touched (A's encR_kept_reg) *)
Lemma encR_kept_reg : forall (E : env) ss msx (regsX : bvmap 5 word) (rr : bv 5),
  st_ok tfibsegs E ss (restrict (w_H Wc) msx) ->
  sr_get (ss_regs ss) rr = SOff (Z.to_nat (bv_unsigned rr)) 0 ->
  ew E (Z.to_nat (bv_unsigned rr)) = getr regsX rr ->
  getr (ms_regs msx) rr = getr regsX rr.
Proof.
intros E ss msx regsX rr HS Hsr Hew.
rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) E ss msx rr HS), Hsr, fsw_SOff0. exact Hew.
Qed.

(* the round's shent list at a state whose env reads the round's registers (A11 / A12 / A31 / A18 in context) *)
Local Ltac enc_shbase memx HAx rr HrA HrB HARUx A11x A12x A31x A18x :=
  apply (encR_sh0 memx _ _ rr HAx HrA HrB HARUx); apply encR_U_of_bv;
  first [ solve [repeat (rewrite ew_ewset_other by lia); rewrite A18x; apply unsigned_lit_small;
                 unfold SHADOW_OFF; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A12x; apply unsigned_lit_small; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A31x; apply unsigned_lit_small;
                 unfold enc_size in *; lia]
        | solve [repeat (rewrite ew_ewset_other by lia); rewrite A11x; apply unsigned_lit_small;
                 unfold enc_size in *; lia]
        | solve [unfold SHADOW_OFF; lia] | solve [unfold enc_size in *; lia] | solve [lia] ].
(* a table seat's shent at a state whose env reads the shadow base s2 (A18x) and holds the seat on atom n *)
Local Ltac enc_shseat memx HAx n idx A18x :=
  apply (encR_shent_seat memx _ n idx HAx);
  first [ solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite A18x;
                   apply unsigned_lit_small; unfold SHADOW_OFF; lia | unfold SHADOW_OFF; lia]]
        | solve [apply encR_U_of_bv; [repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same;
                   apply unsigned_lit_small; unfold G_B64; lia | unfold G_B64; lia]]
        | solve [lia] ].
(* the write-window obligation of a round run: read-only regions, then the output quad on atom 31 inside the
   output block *)
Local Ltac enc_awr E31x rr :=
  cbn [add_cond enc_seat enc_round_ss add_atom ss_mem];
  repeat (apply awr_ok_cons_ro; [cbn; lia|]);
  first [ apply awr_ok_nil
        | eapply awr_ok_cons_gen with (k := 31%nat) (b := q + 4 * rr);
          [ reflexivity | exact E31x
          | cbn [enc_rout YP09.r_wlo YP09.r_whi]; intros a Ha; left; right; right; left;
            exists (q - HEAD), (enc_size len + HEAD); split; [exact HQB|];
            split; [exact encR_new_block|];
            unfold req_size; destruct (enc_size len + HEAD =? 0) eqn:EQ;
            [apply Z.eqb_eq in EQ; unfold HEAD in *; lia | unfold HEAD, enc_size in *; lia]
          | apply awr_ok_nil ] ].
(* a run frame whose regions write only the output quad on atom 31 keeps every byte outside X *)
Local Ltac enc_frame_out E31x :=
  intros ? (rg & Hrin & Hrg); revert Hrg;
  lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in change L with L' in Hrin end;
  cbn [In] in Hrin; repeat (destruct Hrin as [<-|Hrin]); try (destruct Hrin); intros Hrg;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
  first [ lia | unfold FSW_preset_base64_encode_R.encR_out; rewrite E31x in Hrg; unfold enc_size in *; lia
        | rewrite E31x in Hrg; lia ].

Lemma encR_round_step : forall ms md r b0 b1 b2 (Q : world tfibsegs -> config -> Prop),
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
Proof.
intros ms md r b0 b1 b2 Q Hr Hr3 HINV HR HPRE N0 N1 N2 KNEXT KEXIT.
pose proof HR as (R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R14 & R15 & R16 & R17 & R18 & R31 & Rsp & Rk).
pose proof encR_size_pos as HM. pose proof alloc_ceiling_val as (CR & _).
pose proof encR_out_facts as (HAPq & HQceil & HQimg).
assert (HQlo : 4112 <= q) by (unfold HEAD in *; lia).
destruct HINV as (HJ & HARU & HA). unfold FSW_preset_base64_encode_R.encR_J in HJ.
destruct (encR_round_state ms md r b0 b1 b2 Hr Hr3 (conj HJ (conj HARU HA)) HR N0 N1 N2)
  as (HS & B0 & B1 & B2).
destruct (encR_round_env ms r b0 b1 b2 HR) as (A9 & A11 & A12 & A14 & A15 & A18 & A31).
assert (A36 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 36 = w64 b0)
  by (change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A37 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 37 = w64 b1)
  by (change 37%nat with (32 + 5)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (A38 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 38 = w64 b2)
  by (change 38%nat with (32 + 6)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (U18 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) enc_Bx = SHADOW_OFF)
  by (apply (U_atom _ 18 _ A18); unfold SHADOW_OFF; lia).
assert (U12 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (SOff 12 0) = data + 3 * r + 2)
  by (apply (U_atom _ 12 _ A12); lia).
assert (U31 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (SOff 31 0) = q + 4 * r)
  by (apply (U_atom _ 31 _ A31); unfold enc_size in *; lia).
assert (U11 : U (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) (SOff 11 0) = q + 4 * r)
  by (apply (U_atom _ 11 _ A11); unfold enc_size in *; lia).
assert (E31u : bv_unsigned (ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 31) = q + 4 * r)
  by (rewrite A31; apply unsigned_lit_small; unfold enc_size in *; lia).
assert (SHOK : sh_ok tfibsegs enc_Bx enc_SH (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2))
  (mrestrict (w_H Wc) (ms_mem ms)))
  by exact (encR_sh0 (ms_mem ms) md _ r HA Hr Hr3 HARU U18 U12 U31 U11).
(* segment A: 0x84788 -> 0x84800, the three input shadow checks (0x847b0, 0x847d8, 0x847ec), the UBSan deciders
   0x8478c 0x84798 0x8479c 0x847b8 0x847bc 0x847f4 0x847f8, and the first table index (a2 = g_b64 + b0 / 4) *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84800.
all: first [ solve [enc_awr E31u r] | idtac ].
(* the run wrote only inside the output block, so the invariant's agreement survives it *)
assert (HA0 : encR_agree (ms_mem ms0)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms) (ms_mem ms0) encR_out HF); [exact (HA x Hx) | | exact Hx].
  enc_frame_out E31u. }
(* seat 100: a2 = g_b64 + b0 / 4 *)
destruct (enc_ix_range b0 b1 b2 B0 B1 B2) as (X0 & X1 & X2 & X3).
assert (RA1 : getr (ms_regs ms0) 12 = w64 (G_B64 + b0 / 4)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms0 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply FSW_preset_base64_encode_W.enc_denot_of_U. apply (FSW_preset_base64_encode_W.enc_U_addG _ 14 _ (b0 / 4)).
  - repeat (rewrite ew_ewset_other by lia). exact A14.
  - apply (FSW_preset_base64_encode_W.enc_U_t0 _ 36 b0); [repeat (rewrite ew_ewset_other by lia); exact A36 | lia].
  - lia. }
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E12u0 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E31u0 : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
pose proof (encR_seat_ok ms0 _ _ 12%bv 100%nat (b0 / 4) r _ [] HA0 HARU Hr Hr3 ltac:(lia) HS
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA1 E12u0 E31u0
  ltac:(vm_compute; reflexivity)) as HS1.
lazymatch type of HS1 with st_ok _ ?EE2 _ _ =>
  assert (SHOK1 : sh_ok tfibsegs enc_Bx enc_SH1 EE2 (mrestrict (w_H Wc) (ms_mem ms0)))
  by (unfold enc_SH1; apply (proj2 (Forall_app _ enc_SH [mkSHE 100 0 1])); split;
      [ enc_shbase (ms_mem ms0) HA0 r Hr Hr3 HARU A11 A12 A31 A18
      | apply Forall_cons; [enc_shseat (ms_mem ms0) HA0 100%nat (b0 / 4) A18 | apply Forall_nil] ])
end.
clear HS SHOK. rename HS1 into HS. rename SHOK1 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E31B : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
(* segment B: 0x84800 -> 0x84850, the seat's byte and the first output byte (checks 0x84810, 0x84824; UBSan
   0x84840 0x84848), the second index (a2 = g_b64 + idx1) *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84850.
all: first [ solve [enc_awr E31B r] | idtac ].
(* the seat the run is done with is dropped, the next one is seated, and the agreement is re-read *)
assert (HA1 : encR_agree (ms_mem ms1)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms0) (ms_mem ms1) encR_out HF0); [exact (HA0 x Hx) | | exact Hx].
  enc_frame_out E31B. }
pose proof ((fun Hm => FSW_preset_base64_encode_W.enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity))
  as HSd1.
assert (RA2 : getr (ms_regs ms1) 12 = w64 (G_B64 + ((b0 mod 4) * 16 + b1 / 16))).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms1 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply FSW_preset_base64_encode_W.enc_denot_of_U.
  apply (FSW_preset_base64_encode_W.enc_U_addG _ 14 _ ((b0 mod 4) * 16 + b1 / 16)).
  - repeat (rewrite ew_ewset_other by lia). exact A14.
  - apply (FSW_preset_base64_encode_W.enc_U_t1 _ 36 37 b0 b1);
      [repeat (rewrite ew_ewset_other by lia); exact A36
      | repeat (rewrite ew_ewset_other by lia); exact A37 | lia | lia].
  - lia. }
lazymatch type of HSd1 with st_ok _ ?EE _ _ =>
  assert (E12u1 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E31u1 : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
pose proof (encR_seat_ok ms1 _ _ 12%bv 200%nat ((b0 mod 4) * 16 + b1 / 16) r _
  [YP09.mkChunk 0 (CVal 1 (SOff 101 0))] HA1 HARU Hr Hr3 ltac:(lia) HSd1
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA2 E12u1 E31u1
  ltac:(vm_compute; reflexivity)) as HS2.
lazymatch type of HS2 with st_ok _ ?EE2 _ _ =>
  assert (SHOK2 : sh_ok tfibsegs enc_Bx enc_SH2 EE2 (mrestrict (w_H Wc) (ms_mem ms1)))
  by (unfold enc_SH2; apply (proj2 (Forall_app _ enc_SH1 [mkSHE 200 0 1])); split;
      [ unfold enc_SH1; apply (proj2 (Forall_app _ enc_SH [mkSHE 100 0 1])); split;
        [ enc_shbase (ms_mem ms1) HA1 r Hr Hr3 HARU A11 A12 A31 A18
        | apply Forall_cons; [enc_shseat (ms_mem ms1) HA1 100%nat (b0 / 4) A18 | apply Forall_nil] ]
      | apply Forall_cons;
        [enc_shseat (ms_mem ms1) HA1 200%nat ((b0 mod 4) * 16 + b1 / 16) A18 | apply Forall_nil] ])
end.
clear HS SHOK HSd1. rename HS2 into HS. rename SHOK2 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E31C : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
(* segment C: 0x84850 -> 0x84898, the second output byte (checks 0x8485c, 0x84874; UBSan 0x84888 0x84890) *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84898.
all: first [ solve [enc_awr E31C r] | idtac ].
assert (HA2 : encR_agree (ms_mem ms2)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms1) (ms_mem ms2) encR_out HF1); [exact (HA1 x Hx) | | exact Hx].
  enc_frame_out E31C. }
pose proof ((fun Hm => FSW_preset_base64_encode_W.enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity))
  as HSd2.
assert (RA3 : getr (ms_regs ms2) 12 = w64 (G_B64 + ((b1 mod 16) * 4 + b2 / 64))).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms2 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply FSW_preset_base64_encode_W.enc_denot_of_U.
  apply (FSW_preset_base64_encode_W.enc_U_addG _ 14 _ ((b1 mod 16) * 4 + b2 / 64)).
  - repeat (rewrite ew_ewset_other by lia). exact A14.
  - apply (FSW_preset_base64_encode_W.enc_U_t2 _ 37 38 b1 b2);
      [repeat (rewrite ew_ewset_other by lia); exact A37
      | repeat (rewrite ew_ewset_other by lia); exact A38 | lia | lia].
  - lia. }
lazymatch type of HSd2 with st_ok _ ?EE _ _ =>
  assert (E12u2 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E31u2 : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
pose proof (encR_seat_ok ms2 _ _ 12%bv 300%nat ((b1 mod 16) * 4 + b2 / 64) r _
  [YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))]
  HA2 HARU Hr Hr3 ltac:(lia) HSd2
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA3 E12u2 E31u2
  ltac:(vm_compute; reflexivity)) as HS3.
lazymatch type of HS3 with st_ok _ ?EE2 _ _ =>
  assert (SHOK3 : sh_ok tfibsegs enc_Bx enc_SH3 EE2 (mrestrict (w_H Wc) (ms_mem ms2)))
  by (unfold enc_SH3; apply (proj2 (Forall_app _ enc_SH2 [mkSHE 300 0 1])); split;
      [ unfold enc_SH2; apply (proj2 (Forall_app _ enc_SH1 [mkSHE 200 0 1])); split;
        [ unfold enc_SH1; apply (proj2 (Forall_app _ enc_SH [mkSHE 100 0 1])); split;
          [ enc_shbase (ms_mem ms2) HA2 r Hr Hr3 HARU A11 A12 A31 A18
          | apply Forall_cons; [enc_shseat (ms_mem ms2) HA2 100%nat (b0 / 4) A18 | apply Forall_nil] ]
        | apply Forall_cons;
          [enc_shseat (ms_mem ms2) HA2 200%nat ((b0 mod 4) * 16 + b1 / 16) A18 | apply Forall_nil] ]
      | apply Forall_cons;
        [enc_shseat (ms_mem ms2) HA2 300%nat ((b1 mod 16) * 4 + b2 / 64) A18 | apply Forall_nil] ])
end.
clear HS SHOK HSd2. rename HS3 into HS. rename SHOK3 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E31D : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
(* segment D: 0x84898 -> 0x848d8, the third output byte (checks 0x848a4, 0x848bc; UBSan 0x848c8 0x848d0) *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x848d8.
all: first [ solve [enc_awr E31D r] | idtac ].
assert (HA3 : encR_agree (ms_mem ms3)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms2) (ms_mem ms3) encR_out HF2); [exact (HA2 x Hx) | | exact Hx].
  enc_frame_out E31D. }
pose proof ((fun Hm => FSW_preset_base64_encode_W.enc_drop_head _ _ _ _ _ Hm HS) ltac:(vm_compute; reflexivity))
  as HSd3.
assert (RA4 : getr (ms_regs ms3) 12 = w64 (G_B64 + b2 mod 64)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H Wc) _ _ ms3 12%bv HS).
  lazymatch goal with |- sv_denot _ ?t = _ => let t' := eval vm_compute in t in change t with t' end.
  apply FSW_preset_base64_encode_W.enc_denot_of_U.
  apply (FSW_preset_base64_encode_W.enc_U_addG _ 14 _ (b2 mod 64)).
  - repeat (rewrite ew_ewset_other by lia). exact A14.
  - apply (FSW_preset_base64_encode_W.enc_U_t3 _ 38 b2); [repeat (rewrite ew_ewset_other by lia); exact A38 | lia].
  - lia. }
lazymatch type of HSd3 with st_ok _ ?EE _ _ =>
  assert (E12u3 : bv_unsigned (ew EE 12) = data + 3 * r + 2)
    by (repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia);
  assert (E31u3 : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
pose proof (encR_seat_ok ms3 _ _ 12%bv 400%nat (b2 mod 64) r _
  [YP09.mkChunk 2 (CVal 1 (SOff 301 0)); YP09.mkChunk 1 (CVal 1 (SOff 201 0));
   YP09.mkChunk 0 (CVal 1 (SOff 101 0))]
  HA3 HARU Hr Hr3 ltac:(lia) HSd3
  ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(lia) RA4 E12u3 E31u3
  ltac:(vm_compute; reflexivity)) as HS4.
lazymatch type of HS4 with st_ok _ ?EE2 _ _ =>
  assert (SHOK4 : sh_ok tfibsegs enc_Bx enc_SH4 EE2 (mrestrict (w_H Wc) (ms_mem ms3)))
  by (unfold enc_SH4; apply (proj2 (Forall_app _ enc_SH3 [mkSHE 400 0 1])); split;
      [ unfold enc_SH3; apply (proj2 (Forall_app _ enc_SH2 [mkSHE 300 0 1])); split;
        [ unfold enc_SH2; apply (proj2 (Forall_app _ enc_SH1 [mkSHE 200 0 1])); split;
          [ unfold enc_SH1; apply (proj2 (Forall_app _ enc_SH [mkSHE 100 0 1])); split;
            [ enc_shbase (ms_mem ms3) HA3 r Hr Hr3 HARU A11 A12 A31 A18
            | apply Forall_cons; [enc_shseat (ms_mem ms3) HA3 100%nat (b0 / 4) A18 | apply Forall_nil] ]
          | apply Forall_cons;
            [enc_shseat (ms_mem ms3) HA3 200%nat ((b0 mod 4) * 16 + b1 / 16) A18 | apply Forall_nil] ]
        | apply Forall_cons;
          [enc_shseat (ms_mem ms3) HA3 300%nat ((b1 mod 16) * 4 + b2 / 64) A18 | apply Forall_nil] ]
      | apply Forall_cons; [enc_shseat (ms_mem ms3) HA3 400%nat (b2 mod 64) A18 | apply Forall_nil] ])
end.
clear HS SHOK HSd3. rename HS4 into HS. rename SHOK4 into SHOK.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E31E : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
(* segment E: 0x848d8 -> 0x84910, the fourth output byte (checks 0x848e4, 0x848fc) and the three counters *)
fsw_aj_run_to_tokU fsw_wr_tbl_ok HS HJ HARU SHOK fs_Bspan 0x84910.
all: first [ solve [enc_awr E31E r] | idtac ].
assert (HA4 : encR_agree (ms_mem ms4)).
{ intros x Hx.
  rewrite (enc_frame_X _ _ (ms_mem ms3) (ms_mem ms4) encR_out HF3); [exact (HA3 x Hx) | | exact Hx].
  enc_frame_out E31E. }
(* the five runs of the round wrote only this round's four output bytes *)
assert (KEEPR : forall a, 0 <= a < 2 ^ 64 -> ~ (q + 4 * r <= a < q + 4 * r + 4) ->
  mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms)) a).
{ intros a Ha Hx. unfold mbyte.
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr3
    ltac:(enc_frame_out E31E) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr2
    ltac:(enc_frame_out E31D) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr1
    ltac:(enc_frame_out E31C) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr0
    ltac:(enc_frame_out E31B) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  rewrite (enc_frame_X _ _ _ _ (fun x => q + 4 * r <= x < q + 4 * r + 4) HFr
    ltac:(enc_frame_out E31u) (Z_to_bv 64 a) ltac:(rewrite (wz a Ha); exact Hx)).
  reflexivity. }
(* the four output bytes of the round, read off the output region's chunks *)
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (E31F : bv_unsigned (ew EE 31) = q + 4 * r)
    by (repeat (rewrite ew_ewset_other by lia); exact E31u)
end.
pose proof (fsw_region_nth _ _ (restrict (w_H Wc) ms4) 2
  (YP09.mkRegion (Some 31%nat) 0 4 0 4
     [YP09.mkChunk 3 (CVal 1 (SOff 401 0)); YP09.mkChunk 2 (CVal 1 (SOff 301 0));
      YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))])
  HS ltac:(vm_compute; reflexivity)) as HRout.
cbn [ms_mem restrict] in HRout.
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (VQ : forall (od : Z) (n : nat) v,
    In (YP09.mkChunk od (CVal 1 (SOff n 0)))
       [YP09.mkChunk 3 (CVal 1 (SOff 401 0)); YP09.mkChunk 2 (CVal 1 (SOff 301 0));
        YP09.mkChunk 1 (CVal 1 (SOff 201 0)); YP09.mkChunk 0 (CVal 1 (SOff 101 0))] ->
    sv_denot EE (SOff n 0) = Z_to_bv 64 v -> 0 <= v < 256 ->
    val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + od) 1 v)
  by (intros od n v Hin Hd Hv;
      exact (fsw_field _ _ 31 (q + 4 * r) _ 0 4 0 4 od 1%N (SOff n 0) v HRout E31F Hin Hd
        ltac:(cbn [Z.of_N]; lia) ltac:(cbn [Z.of_N]; lia)))
end.
assert (VO0 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 0) 1
  (WriterSpec.b64c (b0 / 4)))
  by (apply (VQ 0 101%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range (b0 / 4) ltac:(lia)); lia]).
assert (VO1 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 1) 1
  (WriterSpec.b64c ((b0 mod 4) * 16 + b1 / 16)))
  by (apply (VQ 1 201%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range ((b0 mod 4) * 16 + b1 / 16) ltac:(lia)); lia]).
assert (VO2 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 2) 1
  (WriterSpec.b64c ((b1 mod 16) * 4 + b2 / 64)))
  by (apply (VQ 2 301%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range ((b1 mod 16) * 4 + b2 / 64) ltac:(lia)); lia]).
assert (VO3 : val_mem tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) (q + 4 * r + 3) 1
  (WriterSpec.b64c (b2 mod 64)))
  by (apply (VQ 3 401%nat); [cbn; tauto
      | rewrite fsw_SOff0; repeat (rewrite ew_ewset_other by lia); rewrite ew_ewset_same; reflexivity
      | pose proof (b64c_range (b2 mod 64) ltac:(lia)); lia]).
(* the base64 text written so far gains this round's four letters *)
destruct (encR_prefix_step r b0 b1 b2 Hr Hr3 N0 N1 N2) as (HMODEL & HLEN4).
assert (HPRE' : garr8 tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) q
  (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs))).
{ rewrite HMODEL.
  apply (encR_garr8_app4 _ _ _ _ _ _ q (4 * r));
    first [ solve [apply (encR_garr8_keep (mrestrict (w_H Wc) (ms_mem ms)) _ q _
                     (fun x => q + 4 * r <= x < q + 4 * r + 4) KEEPR ltac:(lia)
                     ltac:(rewrite HLEN4; unfold enc_size in *; lia)
                     ltac:(intros i Hi; rewrite HLEN4 in Hi; lia) HPRE)]
          | solve [exact HLEN4] | solve [lia] | solve [unfold enc_size in *; lia]
          | solve [exact VO0] | solve [exact VO1] | solve [exact VO2] | solve [exact VO3]
          | solve [pose proof (b64c_range (b0 / 4) ltac:(lia)); lia]
          | solve [pose proof (b64c_range ((b0 mod 4) * 16 + b1 / 16) ltac:(lia)); lia]
          | solve [pose proof (b64c_range ((b1 mod 16) * 4 + b2 / 64) ltac:(lia)); lia]
          | solve [pose proof (b64c_range (b2 mod 64) ltac:(lia)); lia] ]. }
(* the loop's branch: `bltu a5, s0` at 0x84910 *)
assert (A8 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 8 = w64 len)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 8 8%bv eq_refl); exact R8).
assert (A10 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 10 = w64 q)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 10 10%bv eq_refl); exact R10).
assert (A16 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 16 = w64 (18446744073709551615 - data))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 16 16%bv eq_refl); exact R16).
assert (A17 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 17 = w64 (data + 1))
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 17 17%bv eq_refl); exact R17).
assert (A2 : ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) 2 = getr (ms_regs ms) 2)
  by (rewrite (ew_Ereg_nat (ms_regs ms) _ 2 2%bv eq_refl); reflexivity).
lazymatch type of HS with st_ok _ ?EE _ _ =>
  assert (U15F : U EE (SOff 15 3) = 3 * r + 5)
    by (replace (3 * r + 5) with (3 * r + 2 + 3) by lia;
        apply (U_atom_off _ 15 (3 * r + 2) 3);
        [repeat (rewrite ew_ewset_other by lia); exact A15 | lia | lia]);
  assert (U8F : U EE (SOff 8 0) = len)
    by (apply (U_atom _ 8 len); [repeat (rewrite ew_ewset_other by lia); exact A8 | lia])
end.
(* a callee-saved register other than sp, s0, s1, s2, s3, s4 is the entry's: the round's runs never write it *)
assert (KEPTF : forall msx ssx (EX : env),
  st_ok tfibsegs EX ssx (restrict (w_H Wc) msx) ->
  (forall rr : bv 5, In rr [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv ->
     sr_get (ss_regs ssx) rr = SOff (Z.to_nat (bv_unsigned rr)) 0) ->
  (forall n, (n < 32)%nat -> ew EX n = ew (Ereg (ms_regs ms) (encR_extra3 b0 b1 b2)) n) ->
  FSW_preset_base64_encode_R.encR_kept regs0 msx).
{ intros msx ssx EX HSx Hsr Hew z Hz H2 H8 H9 H18 H19 H20.
  pose proof (Rk z Hz H2 H8 H9 H18 H19 H20) as RkZ. rewrite <- RkZ.
  assert (Hc : z = 3 \/ z = 4 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27)
    by (unfold acallee_saved in Hz; lia).
  assert (Hin : In (Z_to_bv 5 z) [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv)
    by (repeat (destruct Hc as [Hc|Hc]); subst z; cbn [In];
        repeat first [ solve [left; apply bv_eq; vm_compute; reflexivity] | right ]).
  apply (encR_kept_reg EX ssx msx (ms_regs ms) _ HSx (Hsr _ Hin)).
  assert (Hz5 : (Z.to_nat (bv_unsigned (Z_to_bv 5 z)) < 32)%nat)
    by (rewrite Z_to_bv_unsigned, bv_wrap_small;
        [unfold acallee_saved in Hz; lia | change (bv_modulus 5) with 32; unfold acallee_saved in Hz; lia]).
  rewrite (Hew _ Hz5). apply ew_Ereg_reg. }
eapply SRr_sym_branch with (c := BC_LTU) (a := SOff 15 3) (b := SOff 8 0);
  [exact HS | intros Hbr HSb | intros Hbr HSb];
  rewrite branch_ltu_U, U15F, U8F in Hbr.
- (* taken: the loop goes round again, 0x84910 -> 0x84784 `add a2,s1,a5` -> the head 0x84788 *)
  apply Z.ltb_lt in Hbr.
  clear HS. rename HSb into HS.
  (* the last instructions of the round store nothing: drop the three regions, so the run keeps every byte *)
  do 3 (let H' := fresh "HSd" in
        pose proof ((fun Hm => FSW_preset_base64_encode_W.enc_drop_head _ _ _ _ _ Hm HS)
          ltac:(vm_compute; reflexivity)) as H';
        clear HS; rename H' into HS).
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU 0x84788.
  all: first [ solve [cbn [add_cond ss_mem]; apply awr_ok_nil] | idtac ].
  apply (KNEXT ms5 _ ltac:(lia)).
  + split; [|split].
    * unfold FSW_preset_base64_encode_R.encR_J. exact HJ.
    * exact HARU.
    * intros x Hx.
      rewrite (enc_frame_X _ _ (ms_mem ms4) (ms_mem ms5) encR_out HF4); [exact (HA4 x Hx) | | exact Hx].
      intros a (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin.
  + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split; [|split;
      [|split; [|split; [|split; [|split; [|split]]]]]]]]]]]]]].
    * exact (fsw_reg_lit _ _ _ _ 5%bv 1 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
    * exact (fsw_reg_lit _ _ _ _ 6%bv 18446744073709416351 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
    * exact (fsw_reg_lit _ _ _ _ 7%bv 18446744073709551615 HS ltac:(vm_compute; reflexivity) ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 8%bv 8 len HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A8; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 9%bv 9 data HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A9; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A10; apply unsigned_lit_small;
                     unfold enc_size in *; lia) ltac:(unfold enc_size in *; lia)).
    * replace (q + 4 * (r + 1)) with (q + 4 * r + 4) by lia.
      exact (FSW_preset_base64_encode_W.enc_reg_val _ _ _ _ 11%bv 11 4 (q + 4 * r) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A11; apply unsigned_lit_small;
                     unfold enc_size in *; lia) ltac:(unfold enc_size in *; lia)).
    * (* 0x84784 `add a2,s1,a5`: the alias s1 + a5 -> a2 gives atom 12 + 3 *)
      replace (data + 3 * (r + 1) + 2) with (data + 3 * r + 2 + 3) by lia.
      exact (FSW_preset_base64_encode_W.enc_reg_val _ _ _ _ 12%bv 12 3 (data + 3 * r + 2) HS
               ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A12; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 14%bv 14 G_B64 HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A14; apply unsigned_lit_small;
                     unfold G_B64; lia) ltac:(unfold G_B64; lia)).
    * replace (3 * (r + 1) + 2) with (3 * r + 2 + 3) by lia.
      exact (FSW_preset_base64_encode_W.enc_reg_val _ _ _ _ 15%bv 15 3 (3 * r + 2) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A15; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 16%bv 16 (18446744073709551615 - data) HS
               ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A16; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 17%bv 17 (data + 1) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A17; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A18; apply unsigned_lit_small;
                     unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
    * replace (q + 4 * (r + 1)) with (q + 4 * r + 4) by lia.
      exact (FSW_preset_base64_encode_W.enc_reg_val _ _ _ _ 31%bv 31 4 (q + 4 * r) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); exact E31u) ltac:(unfold enc_size in *; lia)).
    * unfold spZ. rewrite (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
        ltac:(vm_compute; reflexivity)
        ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A2; reflexivity)
        ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia)).
      unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small;
        [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
         pose proof (u64_range (getr (ms_regs ms) 2)); lia].
    * apply (KEPTF ms5 _ _ HS).
      -- intros rr Hin. cbn [In] in Hin.
         repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; vm_compute; reflexivity.
      -- intros n Hn. repeat (rewrite ew_ewset_other by lia). reflexivity.
  + exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms5 HS ltac:(vm_compute; reflexivity)).
  + assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a).
    { intros a Ha _. unfold mbyte. rewrite (HFr4 (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin. }
    assert (HL5 : Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs))) = 4 * r + 4)
      by (rewrite HMODEL, length_app; cbn [length]; rewrite Nat2Z.inj_add, HLEN4; lia).
    apply (encR_garr8_keep _ _ q _ (fun _ => False) KEEP5);
      [ lia | rewrite HL5; unfold enc_size in *; lia | intros i _ F; exact F | exact HPRE' ].
- (* not taken: the loop is done, 0x84910 -> 0x84914 `j 0x849b0` -> `addi a1,t3,4`, `addi a3,a5,-2` -> 0x849b8 *)
  apply Z.ltb_ge in Hbr.
  clear HS. rename HSb into HS.
  do 3 (let H' := fresh "HSd" in
        pose proof ((fun Hm => FSW_preset_base64_encode_W.enc_drop_head _ _ _ _ _ Hm HS)
          ltac:(vm_compute; reflexivity)) as H';
        clear HS; rename H' into HS).
  fsw_aj_run_toU fsw_wr_tbl_ok HS HJ HARU 0x849b8.
  all: first [ solve [cbn [add_cond ss_mem]; apply awr_ok_nil] | idtac ].
  apply (KEXIT ms5 _ ltac:(lia)).
  + split; [|split].
    * unfold FSW_preset_base64_encode_R.encR_J. exact HJ.
    * exact HARU.
    * intros x Hx.
      rewrite (enc_frame_X _ _ (ms_mem ms4) (ms_mem ms5) encR_out HF4); [exact (HA4 x Hx) | | exact Hx].
      intros a (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin.
  + split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 8%bv 8 len HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A8; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 9%bv 9 data HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A9; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 10%bv 10 q HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A10; apply unsigned_lit_small;
                     unfold enc_size in *; lia) ltac:(unfold enc_size in *; lia)).
    * replace (q + 4 * (r + 1)) with (q + 4 * r + 4) by lia.
      exact (FSW_preset_base64_encode_W.enc_reg_val _ _ _ _ 11%bv 31 4 (q + 4 * r) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); exact E31u) ltac:(unfold enc_size in *; lia)).
    * replace (3 * (r + 1)) with (3 * r + 2 + 1) by lia.
      exact (FSW_preset_base64_encode_W.enc_reg_val _ _ _ _ 13%bv 15 1 (3 * r + 2) HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A15; apply unsigned_lit_small; lia)
               ltac:(lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 14%bv 14 G_B64 HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A14; apply unsigned_lit_small;
                     unfold G_B64; lia) ltac:(unfold G_B64; lia)).
    * exact (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 18%bv 18 SHADOW_OFF HS ltac:(vm_compute; reflexivity)
               ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A18; apply unsigned_lit_small;
                     unfold SHADOW_OFF; lia) ltac:(unfold SHADOW_OFF; lia)).
    * unfold spZ. rewrite (FSW_preset_base64_encode_W.enc_reg_val0 _ _ _ _ 2%bv 2 (spZ (ms_regs ms)) HS
        ltac:(vm_compute; reflexivity)
        ltac:(repeat (rewrite ew_ewset_other by lia); rewrite A2; reflexivity)
        ltac:(unfold spZ; pose proof (u64_range (getr (ms_regs ms) 2)); lia)).
      unfold w64. rewrite Z_to_bv_unsigned, bv_wrap_small;
        [exact Rsp | change (bv_modulus 64) with (2 ^ 64); unfold spZ;
         pose proof (u64_range (getr (ms_regs ms) 2)); lia].
    * apply (KEPTF ms5 _ _ HS).
      -- intros rr Hin. cbn [In] in Hin.
         repeat (destruct Hin as [<-|Hin]); [..|destruct Hin]; vm_compute; reflexivity.
      -- intros n Hn. repeat (rewrite ew_ewset_other by lia). reflexivity.
  + exact (st_ok_restrict_mkst tfibsegs (w_H Wc) _ _ ms5 HS ltac:(vm_compute; reflexivity)).
  + assert (KEEP5 : forall a, 0 <= a < 2 ^ 64 -> ~ False ->
      mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms5)) a = mbyte tfibsegs (mrestrict (w_H Wc) (ms_mem ms4)) a).
    { intros a Ha _. unfold mbyte. rewrite (HFr4 (Z_to_bv 64 a)); [reflexivity|].
      intros (rg & Hrin & _).
      lazymatch type of Hrin with In _ ?L => let L' := eval vm_compute in L in
        change L with L' in Hrin end.
      destruct Hrin. }
    assert (HL5 : Z.of_nat (length (WriterSpec.b64_enc (firstn (Z.to_nat (3 * (r + 1))) bs))) = 4 * r + 4)
      by (rewrite HMODEL, length_app; cbn [length]; rewrite Nat2Z.inj_add, HLEN4; lia).
    apply (encR_garr8_keep _ _ q _ (fun _ => False) KEEP5);
      [ lia | rewrite HL5; unfold enc_size in *; lia | intros i _ F; exact F | exact HPRE' ].
Qed.
(* the contract with lib/B/FSW_preset_base64_encode_loop.v: encR_round_step is its encR_loop's hypothesis RS *)
Check (ltac:(encI (@FSW_preset_base64_encode_loop.encR_loop)) encR_round_step).
End R.

End W.
About encR_round_step.
Print Assumptions encR_round_step.
