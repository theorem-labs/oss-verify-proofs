(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface LayoutPA AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World A_Img A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_HEAD  : Z := 0x8b7fc.   (* [comment removed for export] *)
Definition PC_LATCH : Z := 0x8c728.   (* [comment removed for export] *)
Definition PC_STORE : Z := 0x8c724.   (* [comment removed for export] *)
Definition PC_EXIT  : Z := 0x8d7f8.   (* [comment removed for export] *)
Definition PARSE_FRAME : Z := 304.

(* [comment removed for export] *)
Definition LIT_empty : Z := vi_empty VIA.
Definition LIT_arrow : Z := vi_arrow VIA.          (* [comment removed for export] *)
Definition LIT_cdata_end : Z := vi_cdata_end VIA.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section P.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Record penv : Type := PENV {
    pe_H : henv;              (* [comment removed for export] *)
    pe_VEP : Z; pe_S : Z;     (* [comment removed for export] *)
    pe_b : Z;                 (* [comment removed for export] *)
    pe_flags : Z; pe_wa : Z;  (* [comment removed for export] *)
    pe_DATA : Z; pe_inp : list byte;   (* [comment removed for export] *)
    pe_lo : Z;                (* [comment removed for export] *)
    pe_sp : Z;                (* [comment removed for export] *)
    pe_gp : word; pe_F : bvmap 5 word; pe_fc : bv 32;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pe_ra : word; pe_s0 : word; pe_s1 : word; pe_s2 : word; pe_s3 : word; pe_s4 : word; pe_s5 : word;
    pe_s6 : word; pe_s7 : word; pe_s8 : word; pe_s9 : word; pe_s10 : word; pe_s11 : word;
    (* [comment removed for export] *)
    pe_A0 : AS; pe_v0 : mem; pe_md0 : Model;
    (* [comment removed for export] *)
    pe_SB : Z; pe_NS : Z
  }.
  Definition pe_N (E : penv) : Z := Z.of_nat (length (pe_inp E)).
  Definition pe_e (E : penv) : Z := pe_DATA E + pe_N E.
  Definition pe_fp (E : penv) : Z := pe_sp E - PARSE_FRAME.     (* [comment removed for export] *)

  Definition penv_ok (E : penv) : Prop :=
       henv_geom LPA (pe_H E)
    /\ 0 <= pe_flags E < 16
    /\ 1 <= pe_N E < NMAX
    /\ alloc_ceiling <= pe_lo E /\ pe_lo E + PARSE_STACK <= pe_sp E /\ pe_sp E + 64 <= 2^47 /\ pe_sp E mod 16 = 0
    /\ pe_VEP E <> pe_S E /\ pe_wa E <> pe_S E /\ pe_DATA E <> pe_VEP E /\ pe_DATA E <> pe_S E /\ pe_DATA E <> pe_wa E
    /\ pe_VEP E <> pe_wa E
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    /\ a_livebytes (pe_A0 E) + PARSE_LIVE (pe_N E) <= LIVE_MAX /\ a_nlive (pe_A0 E) + PARSE_NLIVE <= NLIVE_MAX
    /\ lib_frames (pe_A0 E)
    (* [comment removed for export] *)
    /\ a_live (pe_A0 E) (pe_b E) = Some 16 /\ a_live (pe_A0 E) (pe_S E) = Some 40.

  (* [comment removed for export] *)
  Definition pframe (E : penv) (j0 j8 : word) : list cell :=
    let V := pe_VEP E in let wz := fun z => C8 (Z_to_bv 64 z) in
    [ C8 j0; C8 j8;
      wz (V + 256); wz (V + 248); wz (V + 232); wz (V + 224); wz (V + 88); wz (V + 144); wz (V + 24); wz (V + 192);
      wz (V + 264); wz (V + 76); wz (V + 216); wz (V + 272); wz (V + 240); wz (V + 296); wz (V + 92); wz (V + 292);
      wz (V + 200); wz (V + 80); wz (V + 84); wz (V + 184); wz (V + 168); wz (V + 176); wz ((V + 160) / 8 + 2147450880);
      C8 (pe_s11 E); C8 (pe_s10 E); C8 (pe_s9 E); C8 (pe_s8 E); C8 (pe_s7 E); C8 (pe_s6 E); C8 (pe_s5 E);
      C8 (pe_s4 E); C8 (pe_s3 E); C8 (pe_s2 E); C8 (pe_s1 E); C8 (pe_s0 E); C8 (pe_ra E) ].

  Lemma pframe_size : forall E j0 j8, cells_size (pframe E j0 j8) = 304%nat.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record pst : Type := PST {
    x_p : Z;                    (* [comment removed for export] *)
    x_st : vstate;              (* [comment removed for export] *)
    x_v : vep; x_tag : list byte; x_q : vep_pads;   (* [comment removed for export] *)
    x_vv : vsb_rec;             (* [comment removed for export] *)
    x_va : option vsb_rec;      (* [comment removed for export] *)
    x_vi : option vsb_rec       (* [comment removed for export] *)
  }.

  (* [comment removed for export] *)
  Definition look (E : penv) (x : pst) : Z :=
    match nth_error (pe_inp E) (Z.to_nat (x_p x - pe_DATA E)) with Some b => bv_unsigned b | None => 0 end.

  (* [comment removed for export] *)
  Definition in_tag_cluster (x : pst) : Prop :=
    match x_st x with
    | S_InTag | S_Attr | S_SkipAttribute | S_AttrGetValue | S_AttrDelim | S_AttrValue => True
    | S_Match => x_v x Fmatch = vi_tbl_attr_include VIA
    | _ => False
    end.
  Definition attr_states (x : pst) : Prop :=
    match x_st x with S_AttrGetValue | S_AttrDelim | S_AttrValue => True | _ => False end.
  Definition avsb_states (x : pst) : Prop :=
    match x_st x with S_AttrDelim | S_AttrValue | S_TagError => True | _ => False end.

  (* [comment removed for export] *)
  Definition pst_blocks (x : pst) (a : Z) : Prop :=
    a = vb_buf (x_vv x)
    \/ match x_va x with None => False | Some y => a = x_v x Fattr_vsb \/ a = vb_buf y end
    \/ match x_vi x with None => False | Some y => a = x_v x Finclude_src \/ a = vb_buf y end.
  Definition x_vio (x : pst) : option (vsb_rec * bool) := option_map (fun y => (y, true)) (x_vi x).

  (* [comment removed for export] *)
  Definition pzone (E : penv) (x : pst) (a : Z) : Prop :=
    parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E) a \/ parse_new (x_v x) (x_vv x) (x_va x) (x_vio x) a.

  (* [comment removed for export] *)
  Definition oacost (x : pst) : Z := match x_va x with Some y => vb_len y + 8 | None => 0 end.
  Definition oicost (x : pst) : Z := match x_vi x with Some y => vb_len y + 8 | None => 0 end.
  (* [comment removed for export] *)
  Definition walen (x : pst) : Z := match x_va x with Some y => vb_len y | None => 0 end.
  Definition wilen (x : pst) : Z := match x_vi x with Some y => vb_len y | None => 0 end.
  Definition wpot (x : pst) : Z :=
    match x_va x with Some y => vsb_pot y | None => 0 end + match x_vi x with Some y => vsb_pot y | None => 0 end.
  (* [comment removed for export] *)
  Definition wppot (x : pst) : Z :=
    match x_va x with Some y => vsb_ppot y | None => 0 end + match x_vi x with Some y => vsb_ppot y | None => 0 end.
  Definition in_incl_tag (x : pst) : bool :=
    match x_st x with
    | S_InTag | S_Attr | S_SkipAttribute | S_AttrGetValue | S_AttrDelim | S_AttrValue => negb (Z.eqb (x_v x Fattr) 0)
    | S_Match => Z.eqb (x_v x Fmatch) (vi_tbl_attr_include VIA)
    | S_TagError => match x_va x with Some _ => true | None => false end
    | _ => false
    end.
  Definition ptag (x : pst) : Z := if in_incl_tag x then match x_vi x with None => 96 | Some _ => 48 end else 0.
  Definition pbva (x : pst) : Z :=
    if match x_va x with Some _ => true | None => match x_st x with S_AttrGetValue => true | _ => false end end
    then (if Z.eqb (x_v x Fmatch_hit) (vi_tbl_attr_include VIA) then 48 else 96) else 0.
  Definition pbvi (x : pst) : Z := match x_vi x with Some _ => 96 | None => 0 end.
  Definition phead (x : pst) : Z :=
    match x_st x with
    | S_ESITag | S_end_ESITag => 12
    | S_Match => if Z.eqb (x_v x Fmatch) (vi_tbl_esi VIA) then 12 else 0
    | S_ESI_Include => 96
    | _ => 0
    end.
  Definition pbank (x : pst) : Z := ptag x + pbva x + pbvi x + phead x.
  Definition pcharge (E : penv) (x : pst) : Z :=
    (vsb_ppot (x_vv x) - 96) + wppot x + 12 * (x_p x - pe_DATA E - walen x - wilen x) - pbank x.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition va_world (E : penv) (x : pst) (A : AS) (v : mem) : Prop :=
    match x_va x with
    | None => x_v x Fattr_vsb = 0
    | Some y => x_v x Fattr_vsb <> 0 /\ vsb_obj LPA A v (x_v x Fattr_vsb) y false /\
                vb_size y <= vb_len y + 4096 /\ vb_len y <= x_p x - pe_DATA E /\
                vsb_apart (x_v x Fattr_vsb) y [pe_VEP E; pe_wa E; pe_DATA E; pe_S E; vb_buf (x_vv x)]
    end.
  (* [comment removed for export] *)
  Definition vi_world (E : penv) (x : pst) (A : AS) (v : mem) : Prop :=
    match x_vi x with
    | None => x_v x Finclude_src = 0
    | Some y => x_v x Finclude_src <> 0 /\ vsb_obj LPA A v (x_v x Finclude_src) y true /\ vb_error y = 0 /\
                vb_size y <= vb_len y + 4096 /\ vb_len y <= x_p x - pe_DATA E /\
                vsb_apart (x_v x Finclude_src) y [pe_VEP E; pe_wa E; pe_DATA E; pe_S E; vb_buf (x_vv x)] /\
                match x_va x with None => True
                | Some z => vsb_apart (x_v x Finclude_src) y [x_v x Fattr_vsb; vb_buf z] end
    end.

  Record pinvg (d : Z) (E : penv) (x : pst) (A : AS) (v : mem) : Prop := Build_pinvg {   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pi_vep   : vep_obj LPA A v (pe_VEP E) (x_v x) (x_tag x) (x_q x);
    pi_base  : vep_base (pe_H E) (pe_VEP E) (x_v x);
    pi_flags : x_v x Fflags = pe_flags E;
    pi_vsbf  : x_v x Fvsb = pe_S E;
    pi_startup : x_v x Fstartup = 0;
    pi_state : x_v x Fstate = vi_st VIA (x_st x);
    (* [comment removed for export] *)
    pi_cnt   : vep_cnt (x_v x) (x_v x Fver_p - pe_DATA E);
    pi_verp  : pe_DATA E <= x_v x Fver_p <= x_p x;
    pi_pe    : x_p x <= pe_e E;
    (* [comment removed for export] *)
    pi_b01   : bool01 (x_v x Flast_mark) /\ bool01 (x_v x Fesi_found) /\ bool01 (x_v x Fendtag) /\
               bool01 (x_v x Femptytag) /\ bool01 (x_v x Fcanattr) /\ bool01 (x_v x Fremove) /\
               bool01 (x_v x Fin_esi_tag) /\ bool01 (x_v x Finclude_continue);
    pi_tagi  : 0 <= x_v x Ftag_i <= 7;
    pi_delim : (x_st x <> S_AttrValue -> x_v x Fattr_delim = 0) /\
               (x_st x = S_AttrValue -> x_v x Fattr_delim = 32 \/ x_v x Fattr_delim = 34 \/ x_v x Fattr_delim = 39);
    pi_esicmt : (x_v x Fesicmt = 0 /\ x_v x Fesicmt_p = 0) \/
                (x_v x Fesicmt = LIT_arrow /\ LIT_arrow <= x_v x Fesicmt_p <= LIT_arrow + 2);
    pi_until : x_st x = S_Until ->
               (x_v x Funtil = LIT_arrow \/ x_v x Funtil = LIT_cdata_end) /\
               x_v x Funtil <= x_v x Funtil_p <= x_v x Funtil + 2 /\ x_v x Funtil_s = vi_st VIA S_NxtTag;
    pi_match : x_st x = S_Match ->
               x_v x Fmatch = vi_tbl_bom VIA \/ x_v x Fmatch = vi_tbl_starttag VIA \/ x_v x Fmatch = vi_tbl_esi VIA \/
               x_v x Fmatch = vi_tbl_attr_include VIA;
    pi_dostuff : x_v x Fdostuff = 0 \/ x_v x Fdostuff = vi_do_include VIA \/ x_v x Fdostuff = vi_do_remove VIA \/
                 x_v x Fdostuff = vi_do_comment VIA;
    pi_armed : in_tag_cluster x -> x_v x Fdostuff <> 0;
    pi_attr  : x_v x Fattr = 0 \/
               (x_v x Fattr = vi_tbl_attr_include VIA /\ x_v x Fdostuff = vi_do_include VIA /\
                (in_tag_cluster x \/ x_st x = S_TagError \/ x_st x = S_NxtTag \/ x_st x = S_MatchBuf));
    pi_attrst : attr_states x -> (x_st x = S_AttrGetValue \/ x_va x <> None) ->
                x_v x Fattr = vi_tbl_attr_include VIA /\
                (x_v x Fmatch_hit = vi_tbl_attr_include VIA \/ x_v x Fmatch_hit = vi_tbl_attr_include VIA + 16);
    pi_mattr : x_st x = S_Match -> x_v x Fmatch = vi_tbl_attr_include VIA -> x_v x Fattr = vi_tbl_attr_include VIA;
    (* [comment removed for export] *)
    pi_lookA : x_st x = S_Attr -> x_v x Fattr <> 0 -> x_p x < pe_e E -> vct_namestart (look E x) = true;
    pi_lookM : x_st x = S_Match -> x_v x Fmatch = vi_tbl_attr_include VIA -> x_p x < pe_e E -> vct_namestart (look E x) = true;
    (* [comment removed for export] *)
    pi_vsb   : vsb_obj LPA A v (pe_S E) (x_vv x) false;
    pi_room  : vb_size (x_vv x) <= vb_len (x_vv x) + 4096;
    (* [comment removed for export] *)
    pi_out   : vb_len (x_vv x) + oacost x + oicost x + (match x_st x with S_AttrGetValue => 8 | _ => 0 end)
               <= 3 * x_v x Fo_last + 2 * (x_p x - pe_DATA E);   (* [comment removed for export] *)
    pi_apart : vsb_apart (pe_S E) (x_vv x) [pe_VEP E; pe_wa E; pe_DATA E];
    (* [comment removed for export] *)
    pi_walive : a_live A (pe_wa E) = Some 40;
    (* [comment removed for export] *)
    pi_avsb  : x_v x Fattr_vsb <> 0 -> avsb_states x;
    pi_va    : va_world E x A v;
    (* [comment removed for export] *)
    pi_vi    : vi_world E x A v;
    (* [comment removed for export] *)
    pi_data  : data_obj LPA A v (pe_DATA E) (pe_inp E);
    pi_henv  : henv_ok LPA VIA (pe_H E) A v;
    pi_stk   : stk rsegs v (pe_lo E) (pe_fp E);
    pi_frame : exists j0 j8, rw_cells rsegs v (pe_fp E) (pframe E j0 j8);
    pi_mi    : mem_inv rsegs v;
    pi_ss    : stack_shadow LPA v (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64);
    (* [comment removed for export] *)
    pi_lb    : a_livebytes A = a_livebytes (pe_A0 E) - 56 + world_bytes (x_vv x) (x_va x) (x_vio x);
    pi_nl    : a_nlive A = a_nlive (pe_A0 E) + world_nlive (x_va x) (x_vio x);
    pi_tc    : a_tinycred A = a_tinycred (pe_A0 E);
    pi_fr    : frames_same (pe_A0 E) A;
    pi_keep  : forall p k, a_live (pe_A0 E) p = Some k -> p <> pe_b E -> a_live A p = Some k;
    pi_new   : forall p, parse_blocks (x_v x) (x_vv x) (x_va x) (x_vio x) p -> p = pe_b E \/ a_live (pe_A0 E) p = None;
    pi_cf    : cframe LPA (owned (pe_A0 E)) (owned A) (pe_sp E) PARSE_STACK
                      (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                      (parse_new (x_v x) (x_vv x) (x_va x) (x_vio x)) (pe_v0 E) v;
    (* [comment removed for export] *)
    pi_cr0   : PARSE_CRED (pe_N E) <= a_seccred (pe_A0 E);
    pi_wl    : 0 <= walen x /\ 0 <= wilen x /\ walen x + wilen x <= x_p x - pe_DATA E;
    pi_sc    : a_seccred (pe_A0 E) - (vsb_pot (x_vv x) + wpot x + (x_p x - pe_DATA E - walen x - wilen x) / 4096)
                 <= a_seccred A <= a_seccred (pe_A0 E);
    (* [comment removed for export] *)
    pi_pr0   : PARSE_PRIM (pe_N E) <= a_primcred (pe_A0 E);
    pi_phi   : match x_va x with Some y => vsb_phi y | None => True end /\ match x_vi x with Some y => vsb_phi y | None => True end;
    pi_pc    : a_primcred (pe_A0 E) - pcharge E x - d <= a_primcred A <= a_primcred (pe_A0 E)
  }.
  (* [comment removed for export] *)
  Local Notation pinv := (pinvg 0).
  Local Notation Build_pinv := (Build_pinvg 0).
  Arguments pi_vep {d} E x A v _.
  Arguments pi_base {d} E x A v _.
  Arguments pi_flags {d} E x A v _.
  Arguments pi_vsbf {d} E x A v _.
  Arguments pi_startup {d} E x A v _.
  Arguments pi_state {d} E x A v _.
  Arguments pi_cnt {d} E x A v _.
  Arguments pi_verp {d} E x A v _.
  Arguments pi_pe {d} E x A v _.
  Arguments pi_b01 {d} E x A v _.
  Arguments pi_tagi {d} E x A v _.
  Arguments pi_delim {d} E x A v _.
  Arguments pi_esicmt {d} E x A v _.
  Arguments pi_until {d} E x A v _.
  Arguments pi_match {d} E x A v _.
  Arguments pi_dostuff {d} E x A v _.
  Arguments pi_armed {d} E x A v _.
  Arguments pi_attr {d} E x A v _.
  Arguments pi_attrst {d} E x A v _.
  Arguments pi_mattr {d} E x A v _.
  Arguments pi_lookA {d} E x A v _.
  Arguments pi_lookM {d} E x A v _.
  Arguments pi_vsb {d} E x A v _.
  Arguments pi_room {d} E x A v _.
  Arguments pi_out {d} E x A v _.
  Arguments pi_apart {d} E x A v _.
  Arguments pi_walive {d} E x A v _.
  Arguments pi_avsb {d} E x A v _.
  Arguments pi_va {d} E x A v _.
  Arguments pi_vi {d} E x A v _.
  Arguments pi_data {d} E x A v _.
  Arguments pi_henv {d} E x A v _.
  Arguments pi_stk {d} E x A v _.
  Arguments pi_frame {d} E x A v _.
  Arguments pi_mi {d} E x A v _.
  Arguments pi_ss {d} E x A v _.
  Arguments pi_lb {d} E x A v _.
  Arguments pi_nl {d} E x A v _.
  Arguments pi_tc {d} E x A v _.
  Arguments pi_fr {d} E x A v _.
  Arguments pi_keep {d} E x A v _.
  Arguments pi_new {d} E x A v _.
  Arguments pi_cf {d} E x A v _.
  Arguments pi_cr0 {d} E x A v _.
  Arguments pi_wl {d} E x A v _.
  Arguments pi_sc {d} E x A v _.
  Arguments pi_pr0 {d} E x A v _.
  Arguments pi_phi {d} E x A v _.
  Arguments pi_pc {d} E x A v _.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rank (E : penv) (x : pst) : Z :=
    match x_st x with
    | S_Start | S_StartTag => 12
    | S_Match => if x_v x Fmatch =? vi_tbl_attr_include VIA then 3 else if x_v x Fmatch =? vi_tbl_esi VIA then 7 else 11
    | S_BOM => 10
    | S_TestXml | S_end_ESITag => 9
    | S_ESITag => 8
    | S_ESI_Bogon | S_ESI_Include | S_ESI_Remove | S_ESI_Comment => 6
    | S_SkipAttribute => if vct_xmlname (look E x) then 2 else 6
    | S_InTag => 5
    | S_Attr => 4
    | S_Comment | S_CDATA | S_CommentESI | S_AttrGetValue => 3
    | S_AttrDelim => 2
    | S_AttrValue | S_NxtTag | S_NotMyTag | S_Until => 1
    | S_NotXml | S_TagError | S_MatchBuf => 0
    end.
  Definition phi (E : penv) (x : pst) : Z := 16 * (pe_e E - x_p x) + rank E x.

  Lemma rank_bound : forall E x, 0 <= rank E x <= 12.
  Proof. intros E x. unfold rank. destruct (x_st x); try lia; repeat (destruct (_ =? _)); try lia; destruct (vct_xmlname _); lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition loop_ms (E : penv) (pc p : Z) (s8 : word)
      (ra a0 a1 a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 : word) (m : mem) : machine_state :=
    let V := pe_VEP E in
    MS (mkR ra (Z_to_bv 64 (pe_fp E)) (pe_gp E) (cl_tp LPA) (Z_to_bv 64 (V + 168)) (Z_to_bv 64 (V + 184)) (Z_to_bv 64 (V + 84))
            (Z_to_bv 64 V) (Z_to_bv 64 (V + 160)) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (V + 176))
            s2 (Z_to_bv 64 (V + 64)) (Z_to_bv 64 2147450880) s5 (Z_to_bv 64 p)
            (Z_to_bv 64 (V + 208)) s8 (Z_to_bv 64 (V + 4)) (Z_to_bv 64 (pe_e E)) s11 (Z_to_bv 64 (V + 80)) t4 t5 t6)
       (pe_F E) (Z_to_bv 64 pc) (pe_fc E) None m (seg_rom rsegs).
  Definition S8 (E : penv) : word := Z_to_bv 64 ((pe_VEP E + 64) / 8 + 2147450880).

  (* [comment removed for export] *)
  Definition disp_pc (st : vstate) : Z :=
    match st with
    | S_Start => 0x8baa4 | S_BOM => 0x8bb38 | S_TestXml => 0x8bbb8 | S_NotXml => 0x8d7c4 | S_NotMyTag => 0x8bc44
    | S_NxtTag => 0x8bcc0 | S_StartTag => 0x8c0ec | S_Comment => 0x8c140 | S_CommentESI => 0x8c300 | S_CDATA => 0x8c490
    | S_end_ESITag => 0x8c4f8 | S_ESITag => 0x8c52c | S_ESI_Include => 0x8c5ec | S_ESI_Remove => 0x8c6ec
    | S_ESI_Comment => 0x8c730 | S_ESI_Bogon => 0x8c7b4 | S_InTag => 0x8c7dc | S_TagError => 0x8c974 | S_Attr => 0x8c9c4
    | S_SkipAttribute => 0x8cabc | S_AttrGetValue => 0x8cccc | S_AttrDelim => 0x8cd68 | S_AttrValue => 0x8ce74
    | S_Match => 0x8cf64 | S_MatchBuf => 0x8d0b8 | S_Until => 0x8b9c0
    end.
  Definition disp_a1 (st : vstate) (vep : Z) : Z :=
    match st with
    | S_NxtTag => vep + 200 | S_InTag => 0x23908 | S_TagError => 0x23914   (* [comment removed for export] *)
    | _ => vi_st VIA st
    end.
  (* [comment removed for export] *)
  Definition disp_pos (st : vstate) : Z :=
    match st with
    | S_Start | S_BOM | S_TestXml | S_NotXml | S_NotMyTag => 0
    | S_NxtTag | S_StartTag | S_Comment | S_CommentESI | S_CDATA | S_end_ESITag | S_ESITag | S_ESI_Include
    | S_ESI_Remove | S_ESI_Comment | S_ESI_Bogon => 1
    | S_InTag => 2 | S_TagError | S_Attr | S_SkipAttribute => 3 | S_AttrGetValue => 5
    | S_AttrDelim | S_AttrValue | S_Match | S_MatchBuf | S_Until => 6
    end.
  Definition disp_s2 (st : vstate) : option Z :=
    match disp_pos st with 0 => None | _ => Some (vi_st VIA S_NxtTag) end.
  Definition disp_s5 (st : vstate) (vep : Z) : option Z :=
    match disp_pos st with 0 => None | 1 | 2 => Some (Z.shiftr (vep + 208) 3) | _ => Some (vi_st VIA S_TagError) end.
  Definition disp_s11 (st : vstate) (vep : Z) : option Z :=
    match disp_pos st with 0 => None | 1 => Some (Z.shiftr (vep + 200) 3) | _ => Some (vi_st VIA S_InTag) end.
  Definition disp_a2 (st : vstate) (vep : Z) : option Z :=
    match disp_pos st with 5 => Some (vep + 224) | 6 => Some (vep + 232) | _ => None end.
  Definition disp_a6 (st : vstate) (vep : Z) : option Z := match disp_pos st with 5 | 6 => Some (Z.shiftr (vep + 224) 3) | _ => None end.
  Definition disp_t4 (st : vstate) (vep : Z) : option Z := match disp_pos st with 6 => Some (Z.shiftr (vep + 232) 3) | _ => None end.
  Definition oreg (o : option Z) (dflt : word) : word := match o with Some z => Z_to_bv 64 z | None => dflt end.

  Definition head_ms (E : penv) (x : pst) (s8 ra a0 a1 a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 : word) (m : mem) :=
    loop_ms E PC_HEAD (x_p x) s8 ra a0 a1 a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 m.
  Definition latch_ms (E : penv) (x : pst) (ra a0 a1 a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 : word) (m : mem) :=
    loop_ms E PC_LATCH (x_p x) (S8 E) ra a0 a1 a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 m.
  (* [comment removed for export] *)
  Definition call_ms (E : penv) (pc p : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s11 t3 t4 t5 t6 : word) (m : mem) :=
    let V := pe_VEP E in
    MS (mkR ra (Z_to_bv 64 (pe_fp E)) (pe_gp E) (cl_tp LPA) t0 t1 t2
            (Z_to_bv 64 V) (Z_to_bv 64 (V + 160)) a0 a1 a2 a3 a4 a5 a6 a7
            s2 (Z_to_bv 64 (V + 64)) (Z_to_bv 64 2147450880) s5 (Z_to_bv 64 p)
            (Z_to_bv 64 (V + 208)) (S8 E) (Z_to_bv 64 (V + 4)) (Z_to_bv 64 (pe_e E)) s11 t3 t4 t5 t6)
       (pe_F E) (Z_to_bv 64 pc) (pe_fc E) None m (seg_rom rsegs).
  Definition exit_ms (E : penv) (x : pst) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s11 t3 t4 t5 t6 : word) (m : mem) :=
    call_ms E PC_EXIT (x_p x) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s11 t3 t4 t5 t6 m.
  (* [comment removed for export] *)
  Definition disp_ms (E : penv) (x : pst) (ra a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 : word) (m : mem) :=
    let V := pe_VEP E in let st := x_st x in
    loop_ms E (disp_pc st) (x_p x) (S8 E) ra
            (Z_to_bv 64 (vi_st VIA st)) (Z_to_bv 64 (disp_a1 st V)) (oreg (disp_a2 st V) a2) a3 a4 a5
            (oreg (disp_a6 st V) a6)
            (oreg (disp_s2 st) s2) (oreg (disp_s5 st V) s5) (oreg (disp_s11 st V) s11)
            (oreg (disp_t4 st V) t4) t5 t6 m.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition latch_K (E : penv) (x : pst) (T : TSet) : Prop :=
    forall (x' : pst) (A' : AS) (m' : mem) (md' : Model)
           (ra a0 a1 a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 : word),
      pinv E x' A' (aview A' m') -> ainv A' m' md' -> amd_frame (pe_md0 E) md' ->
      (x_p x' < pe_e E -> phi E x' < phi E x /\ x_st x' <> S_MatchBuf) ->
      srealizes rsegs (mkCfg (latch_ms E x' ra a0 a1 a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 m') md') T.

  (* [comment removed for export] *)
  Definition exit_K (E : penv) (T : TSet) : Prop :=
    forall (x' : pst) (A' : AS) (m' : mem) (md' : Model)
           (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s11 t3 t4 t5 t6 : word),
      pinv E x' A' (aview A' m') -> ainv A' m' md' -> amd_frame (pe_md0 E) md' ->
      x_p x' = pe_e E ->
      srealizes rsegs (mkCfg (exit_ms E x' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s11 t3 t4 t5 t6 m') md') T.

  Definition handler_stmt (st : vstate) : Prop :=
    forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
           (ra a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 : word),
      penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md ->
      x_st x = st -> x_p x < pe_e E ->
      latch_K E x T -> exit_K E T ->
      srealizes rsegs (mkCfg (disp_ms E x ra a2 a3 a4 a5 a6 s2 s5 s11 t4 t5 t6 m) md) T.
End P.
Notation pinv := (pinvg 0).   (* [comment removed for export] *)
Notation Build_pinv := (Build_pinvg 0).
(* [comment removed for export] *)
Arguments pi_vep {Clg AI d} E x A v _.
Arguments pi_base {Clg AI d} E x A v _.
Arguments pi_flags {Clg AI d} E x A v _.
Arguments pi_vsbf {Clg AI d} E x A v _.
Arguments pi_startup {Clg AI d} E x A v _.
Arguments pi_state {Clg AI d} E x A v _.
Arguments pi_cnt {Clg AI d} E x A v _.
Arguments pi_verp {Clg AI d} E x A v _.
Arguments pi_pe {Clg AI d} E x A v _.
Arguments pi_b01 {Clg AI d} E x A v _.
Arguments pi_tagi {Clg AI d} E x A v _.
Arguments pi_delim {Clg AI d} E x A v _.
Arguments pi_esicmt {Clg AI d} E x A v _.
Arguments pi_until {Clg AI d} E x A v _.
Arguments pi_match {Clg AI d} E x A v _.
Arguments pi_dostuff {Clg AI d} E x A v _.
Arguments pi_armed {Clg AI d} E x A v _.
Arguments pi_attr {Clg AI d} E x A v _.
Arguments pi_attrst {Clg AI d} E x A v _.
Arguments pi_mattr {Clg AI d} E x A v _.
Arguments pi_lookA {Clg AI d} E x A v _.
Arguments pi_lookM {Clg AI d} E x A v _.
Arguments pi_vsb {Clg AI d} E x A v _.
Arguments pi_room {Clg AI d} E x A v _.
Arguments pi_out {Clg AI d} E x A v _.
Arguments pi_apart {Clg AI d} E x A v _.
Arguments pi_walive {Clg AI d} E x A v _.
Arguments pi_avsb {Clg AI d} E x A v _.
Arguments pi_va {Clg AI d} E x A v _.
Arguments pi_vi {Clg AI d} E x A v _.
Arguments pi_data {Clg AI d} E x A v _.
Arguments pi_henv {Clg AI d} E x A v _.
Arguments pi_stk {Clg AI d} E x A v _.
Arguments pi_frame {Clg AI d} E x A v _.
Arguments pi_mi {Clg AI d} E x A v _.
Arguments pi_ss {Clg AI d} E x A v _.
Arguments pi_lb {Clg AI d} E x A v _.
Arguments pi_nl {Clg AI d} E x A v _.
Arguments pi_tc {Clg AI d} E x A v _.
Arguments pi_fr {Clg AI d} E x A v _.
Arguments pi_keep {Clg AI d} E x A v _.
Arguments pi_new {Clg AI d} E x A v _.
Arguments pi_cf {Clg AI d} E x A v _.
Arguments pi_cr0 {Clg AI d} E x A v _.
Arguments pi_wl {Clg AI d} E x A v _.
Arguments pi_sc {Clg AI d} E x A v _.
Arguments pi_pr0 {Clg AI d} E x A v _.
Arguments pi_phi {Clg AI d} E x A v _.
Arguments pi_pc {Clg AI d} E x A v _.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cover.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition inblk_sh (p n a : Z) : Prop := p <= a < p + n \/ sh p <= a < sh p + (n + 7) / 8.
  Definition vcover (H : henv) (A : AS) (excl : list Z) (V : Z -> Prop) : Prop :=
    forall a, V a -> (exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a)
                     \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  (* [comment removed for export] *)
  Definition hcover (A : AS) (excl : list Z) (V : Z -> Prop) : Prop :=
    forall a, V a -> exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a.

  Lemma hcover_vcover : forall H A excl V, hcover A excl V -> vcover H A excl V.
  Proof. intros H A excl V C a Ha. left. apply C, Ha. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma cover_blk : forall (H : henv) A excl p n a,
    a_live A p = Some n -> ~ In p excl -> blk p n a ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof. intros H A excl p n a L NI [_ R]. left. exists p, n. unfold inblk_sh. auto. Qed.
  Lemma cover_newblk : forall (H : henv) A excl p n a,
    a_live A p = Some n -> ~ In p excl -> newblk p n a ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof. intros H A excl p n a L NI [[_ R]|[_ R]]; left; exists p, n; unfold inblk_sh; auto. Qed.
  Lemma cover_rng : forall (H : henv) A excl p n a,
    a_live A p = Some n -> ~ In p excl -> p <= a < p + n ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof. intros H A excl p n a L NI R. left. exists p, n. unfold inblk_sh. auto. Qed.
  (* [comment removed for export] *)
  Lemma cover_vsc : forall (H : henv) A (excl : list Z) a,
    h_vsc H + 1304 <= a < h_vsc H + 1320 ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof. intros H A excl a R. right. exact R. Qed.
  (* [comment removed for export] *)
  Lemma hcover_newblk : forall A excl p n a,
    a_live A p = Some n -> ~ In p excl -> newblk p n a -> exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a.
  Proof. intros A excl p n a L NI [[_ R]|[_ R]]; exists p, n; unfold inblk_sh; auto. Qed.
  Lemma hcover_rng : forall A excl p n a,
    a_live A p = Some n -> ~ In p excl -> p <= a < p + n -> exists p n, a_live A p = Some n /\ ~ In p excl /\ inblk_sh p n a.
  Proof. intros A excl p n a L NI R. exists p, n. unfold inblk_sh. auto. Qed.

  (* [comment removed for export] *)
  Lemma live_sh_low : forall A m md p n a, ainv A m md -> a_live A p = Some n ->
    sh p <= a < sh p + (n + 7) / 8 -> (2147451392 <= a < sh alloc_ceiling) /\ a < SHMAX.   (* [comment removed for export] *)
  Proof.
    intros A m md p n a AINV L R. (first [ pose proof ((live_geomP LPA A m md p n AINV L)) as dR_1; dand5 dR_1 as K0 P16 [LO _] HI _ | destruct (live_geomP LPA A m md p n AINV L) as (K0 & P16 & [LO _] & HI & _) ]).
    (first [ pose proof ((app_sh_facts LPA p n LO)) as dR_2; dand3 dR_2 as S1 S2 _ | pose proof (app_sh_facts LPA p n LO) as (S1 & S2 & _) ]). pose proof (sh_le_ceiling p n (mod8_of_mod16 p P16) ltac:(lia) HI).
    pose proof sh_ceiling_le_SHMAX. lia.
  Qed.

  Variables (H : henv) (A A' : AS) (m : mem) (md : Model) (v' : mem) (sp' win : Z) (V N : Z -> Prop) (excl : list Z).
  Hypothesis AINV : ainv A m md.
  Hypothesis CF : cframe LPA (owned A) (owned A') sp' win V N (aview A m) v'.
  Hypothesis HFR : hframe LPA A H.
  Hypothesis CEIL : alloc_ceiling <= sp' - win.
  Hypothesis WPOS : 0 <= win.

  (* [comment removed for export] *)
  Lemma cover_not_blk : forall o0 k,
    vcover H A excl V -> In o0 excl -> a_live A o0 = Some k -> forall a, o0 <= a < o0 + k -> ~ V a.
  Proof.
    intros o0 k C IN L a Ha X. destruct HFR as [age HF].
    destruct (C _ X) as [(p & n' & Lp & NI & [R|R])|R].
    - assert (NE : p <> o0) by (intros ->; exact (NI IN)).
      pose proof (as_live_disjoint LPA A m md p n' o0 k AINV Lp L NE). lia.
    - pose proof (live_sh_low A m md p n' a AINV Lp R). pose proof SHMAX_below_highmem.
      (first [ pose proof ((live_geomP LPA A m md o0 k AINV L)) as dR_3; dand4 dR_3 as _ _ LO0 _ | destruct (live_geomP LPA A m md o0 k AINV L) as (_ & _ & LO0 & _) ]). all_app_facts. unhide_app. lia.   (* [comment removed for export] *)
    - pose proof (as_frame_blk_disjoint LPA A m md (h_ff H) HCLASS age o0 k AINV HF L) as D.
      change (fsize HCLASS) with 8192 in D. unfold h_vsc in R. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rw_cells_call_stack : forall a cs,
    vcover H A excl V -> rw_cells rsegs (aview A m) a cs -> sp' <= a -> a + Z.of_nat (cells_size cs) <= 2^64 ->
    rw_cells rsegs v' a cs.
  Proof.
    intros a cs C RC LO HI. destruct HFR as [age HF].
    (first [ pose proof ((as_frame_ok LPA A m md _ _ _ AINV HF)) as dR_5; dand5 dR_5 as _ _ FLO FHI _ | destruct (as_frame_ok LPA A m md _ _ _ AINV HF) as (_ & _ & FLO & FHI & _) ]).
    change (fsize HCLASS) with 8192 in FHI.
    eapply (rw_cells_ccall LPA A A' sp' win V N _ v' CF); [| | exact RC].
    - eapply (crange_stack (L:=LPA) A m md); [exact AINV| lia| exact HI| eapply (rw_cells_mapped LPA); [exact RC| apply (off_image_stack LPA); lia]].
    - split; [right; exact LO|]. intros i Hi X.
      destruct (C _ X) as [(p & n' & Lp & _ & [R|R])|R].
      + (first [ pose proof ((live_geomP LPA A m md p n' AINV Lp)) as dR_6; dand5 dR_6 as _ _ _ PHI _ | destruct (live_geomP LPA A m md p n' AINV Lp) as (_ & _ & _ & PHI & _) ]). lia.
      + pose proof (live_sh_low A m md p n' _ AINV Lp R). pose proof (sh_bound (Clg:=Clg) 0 0 ltac:(lia) ltac:(lia) ltac:(pose proof alloc_ceiling_num; lia)). lia.
      + unfold h_vsc in R. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma henv_call : hcover A excl V ->
    (forall ff k age, a_frame A ff = Some (k, age) -> exists age', a_frame A' ff = Some (k, age')) ->
    henv_ok LPA VIA H A (aview A m) -> henv_ok LPA VIA H A' v'.
  Proof.
    intros C FS HE. eapply (henv_ok_acall_gen H A A'); [exact AINV| exact CF| exact HE| exact CEIL| exact FS|].
    intros a X. (first [ pose proof ((C a X)) as dR_7; dex2 dR_7 as p n; dand3 dR_7 as L _ R | pose proof ((C a X)) as dR_7; dand5 dR_7 as p n L _ R | destruct (C a X) as (p & n & L & _ & R) ]). exists p, n. split; [exact L| exact R].
  Qed.

  (* [comment removed for export] *)
  Lemma vsb_obj_call : forall S vr fin,
    vcover H A excl V -> In S excl -> In (vb_buf vr) excl ->
    a_live A' S = Some 40 -> a_live A' (vb_buf vr) = Some (vb_size vr) ->
    vsb_obj LPA A (aview A m) S vr fin -> vsb_obj LPA A' v' S vr fin.
  Proof.
    intros S vr fin C I1 I2 L1' L2' VO. (first [ pose proof (VO) as dR_8; dand5 dR_8 as _ _ LS LB _ | pose proof VO as (_ & _ & LS & LB & _) ]).
    eapply (vsb_obj_ccall A A' m md v' sp' win V N S vr fin AINV CF VO CEIL L1' L2').
    intros a [X|X]; [eapply (cover_not_blk S 40)| eapply (cover_not_blk (vb_buf vr) (vb_size vr))]; eassumption.
  Qed.

  Lemma vep_obj_call : forall VEP vv tag q,
    vcover H A excl V -> In VEP excl -> a_live A' VEP = Some 312 ->
    vep_obj LPA A (aview A m) VEP vv tag q -> vep_obj LPA A' v' VEP vv tag q.
  Proof.
    intros VEP vv tag q C IN L' VO. pose proof VO as (L & _).
    eapply (vep_obj_ccall LPA A A' m md v' sp' win V N); [exact AINV| exact CF| exact VO| exact CEIL| exact L'|].
    eapply cover_not_blk; eassumption.
  Qed.

  Lemma data_obj_call : forall DATA inp,
    vcover H A excl V -> In DATA excl -> a_live A' DATA = Some (Z.of_nat (length inp)) ->
    data_obj LPA A (aview A m) DATA inp -> data_obj LPA A' v' DATA inp.
  Proof.
    intros DATA inp C IN L' DO. pose proof DO as (L & _).
    eapply (data_obj_ccall LPA A A' m md v' sp' win V N); [exact AINV| exact CF| exact DO| exact CEIL| exact L'|].
    eapply cover_not_blk; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_shadow_call : forall SB NS lo hi,
    vcover H A excl V -> 0 <= lo ->
    stack_shadow LPA (aview A m) SB NS lo hi -> stack_shadow LPA v' SB NS lo hi.
  Proof.
    intros SB NS lo hi C LO0 SSH. (first [ pose proof (SSH) as dR_9; dand6 dR_9 as B N0 Lq Hh SLO T | pose proof SSH as (B & N0 & Lq & Hh & SLO & T) ]).
    (first [ pose proof ((stack_shadow_open _ SB NS lo hi SSH LO0)) as dR_10; dand12 dR_10 as P zs Bz Ezs LZ _ _ _ _ _ SMX TOP | destruct (stack_shadow_open _ SB NS lo hi SSH LO0) as (P & zs & Bz & Ezs & LZ & _ & _ & _ & _ & _ & SMX & TOP) ]).
    destruct HFR as [age HF]. (first [ pose proof ((as_frame_ok LPA A m md _ _ _ AINV HF)) as dR_11; dand4 dR_11 as _ _ FLO _ | destruct (as_frame_ok LPA A m md _ _ _ AINV HF) as (_ & _ & FLO & _) ]).
    pose proof alloc_ceiling_num as ACV.
    split; [| exact (conj N0 (conj Lq (conj Hh (conj SLO T))))]. rewrite <- Ezs.
    eapply (bytes_at_ccall LPA A A' sp' win V N _ v' CF); [| | exact Bz].
    - eapply crange_sshadow; [exact AINV| exact Bz| exact LZ| exact SMX| exact TOP].
    - rewrite LZ. split; [left; unfold kHighMemBeg in *; all_app_facts; unhide_app; lia|]. intros i Hi X.
      destruct (C _ X) as [(p & n' & Lp & _ & [R|R])|R].
      + (first [ pose proof ((live_geomP LPA A m md p n' AINV Lp)) as dR_12; dand4 dR_12 as _ _ PLO _ | destruct (live_geomP LPA A m md p n' AINV Lp) as (_ & _ & PLO & _) ]). unfold kHighMemBeg in *. all_app_facts. unhide_app. lia.
      + pose proof (live_sh_low A m md p n' _ AINV Lp R). unfold kHighMemBeg in *. all_app_facts. unhide_app. lia.
      + unfold h_vsc, kHighMemBeg in *. all_app_facts. unhide_app. lia.
  Qed.
End Cover.

(* [comment removed for export] *)
Section FrameCall.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma pframe_call : forall E A A' m md v' sp' win V N excl j0 j8,
    penv_ok E -> ainv A m md -> cframe LPA (owned A) (owned A') sp' win V N (aview A m) v' -> hframe LPA A (pe_H E) ->
    alloc_ceiling <= sp' - win -> 0 <= win -> sp' <= pe_fp E ->
    vcover (pe_H E) A excl V ->
    rw_cells rsegs (aview A m) (pe_fp E) (pframe E j0 j8) -> rw_cells rsegs v' (pe_fp E) (pframe E j0 j8).
  Proof.
    intros E A A' m md v' sp' win V N excl j0 j8 PE AINV CF HFR CEIL WPOS SP C FR.
    (first [ dand7 PE as _ _ _ _ _ SPH _ | destruct PE as (_ & _ & _ & _ & _ & SPH & _) ]).
    eapply (rw_cells_call_stack (pe_H E) A A' m md v' sp' win V N excl); try eassumption.
    rewrite pframe_size. unfold pe_fp, PARSE_FRAME in *. lia.
  Qed.
End FrameCall.

(* [comment removed for export] *)
Ltac open_pinv PI :=
  destruct PI as [VEPO BASE FLG VSBF STUP STATE CNT VERP PLE B01 TAGI DELIM ESIC UNTL MTCH DOST ARMED ATTR ATTRST
                  MATTR LOOKA LOOKM VSBO ROOM OUT APART WAL AVSB VA VI DATA HENV STK FRAME MI SS
                  LB NL TC FRS KEEP NEW CF CR0 WL SC PR0 PPH PC];   (* [comment removed for export] *)
  unfold walen, wilen, wpot in WL, SC.

(* [comment removed for export] *)
Lemma sc_xfer : forall c0 c P w s P' w' s',
  c0 - (P + w + s / 4096) <= c <= c0 -> P + w + s / 4096 <= P' + w' + s' / 4096 -> c0 - (P' + w' + s' / 4096) <= c <= c0.
Proof. intros; lia. Qed.
Lemma sc_mono : forall c0 c P w s s',
  c0 - (P + w + s / 4096) <= c <= c0 -> 0 <= s <= s' -> c0 - (P + w + s' / 4096) <= c <= c0.
Proof. intros c0 c P w s s' H1 H2. assert (s / 4096 <= s' / 4096) by (apply Z.div_le_mono; lia). lia. Qed.
(* [comment removed for export] *)
Lemma pc_mono : forall c0 c C d C' d', c0 - C - d <= c <= c0 -> C + d <= C' + d' -> c0 - C' - d' <= c <= c0.
Proof. intros; lia. Qed.
Lemma pc_xfer : forall c0 c c' C d C' d' k, c0 - C - d <= c <= c0 -> c - k <= c' <= c -> C + d + k <= C' + d' -> c0 - C' - d' <= c' <= c0.
Proof. intros; lia. Qed.
Lemma pc_eq : forall c0 c c' C d C' d', c0 - C - d <= c <= c0 -> c' = c -> C + d <= C' + d' -> c0 - C' - d' <= c' <= c0.
Proof. intros; lia. Qed.
Lemma pc_eqd : forall c0 c c' C d C' d' k, c0 - C - d <= c <= c0 -> c' = c - k -> 0 <= k -> C + d + k <= C' + d' -> c0 - C' - d' <= c' <= c0.
Proof. intros; lia. Qed.
Lemma ptag_range : forall x, 0 <= ptag x <= 96.   (* [comment removed for export] *)
Proof. intros x; unfold ptag; destruct (in_incl_tag x); [destruct (x_vi x)|]; cbn; lia. Qed.
Lemma div4096_add : forall a b, 0 <= a -> 0 <= b -> a / 4096 + b / 4096 <= (a + b) / 4096.
Proof. intros a b Ha Hb. Z.div_mod_to_equations. lia. Qed.
Lemma vsb_pot_len : forall y, vb_size y <= vb_len y + 4096 -> 0 <= vb_len y -> 0 <= vb_size y -> vsb_pot y <= vb_len y / 4096.
Proof.
  intros y H1 H2 H3. unfold vsb_pot.
  destruct (Z.le_gt_cases (vb_size y) 61440) as [L|G].
  - rewrite Z.max_r by lia. rewrite Z.sub_diag. change (0 / 4096) with 0. apply Z.div_pos; lia.
  - rewrite Z.max_l by lia. apply Z.div_le_mono; lia.
Qed.
