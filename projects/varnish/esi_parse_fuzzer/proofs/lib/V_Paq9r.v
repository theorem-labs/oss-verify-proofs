(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PC_HEAD  : Z := 0x1a020.   (* [comment removed for export] *)
Definition PC_LATCH : Z := 0x1a77c.   (* [comment removed for export] *)
Definition PC_EXIT  : Z := 0x1ab28.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LIT_empty : Z := 0x10ae6.      (* [comment removed for export] *)
Definition LIT_arrow : Z := 0x1108d.      (* [comment removed for export] *)
Definition LIT_cdata_end : Z := 0x10d51.  (* [comment removed for export] *)
Definition LIT_bomwarn : Z := 0x10af9.    (* [comment removed for export] *)
Definition LIT_ltwarn : Z := 0x11d91.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record penv : Type := PENV {
  pe_H : henv;              (* [comment removed for export] *)
  pe_VEP : Z; pe_S : Z;     (* [comment removed for export] *)
  pe_b : Z;                 (* [comment removed for export] *)
  pe_flags : Z; pe_wa : Z;  (* [comment removed for export] *)
  pe_DATA : Z; pe_inp : list byte;   (* [comment removed for export] *)
  pe_lo : Z;                (* [comment removed for export] *)
  pe_gp : word;             (* [comment removed for export] *)
  (* [comment removed for export] *)
  pe_ra : word; pe_s0 : word; pe_s1 : word; pe_s2 : word; pe_s3 : word; pe_s4 : word; pe_s5 : word;
  pe_s6 : word; pe_s7 : word; pe_s8 : word; pe_s9 : word; pe_s10 : word; pe_s11 : word;
  (* [comment removed for export] *)
  pe_LB0 : Z; pe_NL0 : Z
}.
Definition pe_N (E : penv) : Z := Z.of_nat (length (pe_inp E)).
Definition pe_e (E : penv) : Z := pe_DATA E + pe_N E.
Definition pe_sp (E : penv) : Z := h_sp (pe_H E) - 176.     (* [comment removed for export] *)

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition penv_ok (E : penv) : Prop :=
     henv_geom (pe_H E)
  /\ 0 <= pe_flags E < 16
  /\ 1 <= pe_N E < NMAX
  /\ alloc_ceiling <= pe_lo E /\ pe_lo E + PARSE_STACK <= h_sp (pe_H E)
  /\ pe_VEP E <> pe_S E /\ pe_wa E <> pe_S E /\ pe_DATA E <> pe_VEP E /\ pe_DATA E <> pe_S E /\ pe_DATA E <> pe_wa E
  /\ pe_VEP E <> pe_wa E
  /\ bv_unsigned (pe_ra E) mod 2 = 0
  (* [comment removed for export] *)
  /\ pe_LB0 E + PARSE_LIVE (pe_N E) <= LIVE_MAX /\ pe_NL0 E + PARSE_NLIVE <= NLIVE_MAX.

End CEIL.

(* [comment removed for export] *)
Definition pframe (E : penv) (j0 j8 : word) : list cell :=
  [ C8 j0; C8 j8;
    C8 (w64 (pe_VEP E + 256)); C8 (w64 (pe_VEP E + 224));
    C8 (w64 LIT_ltwarn); C8 (w64 LIT_bomwarn); C8 (w64 (st0 S_StartTag)); C8 (w64 (st0 S_Match)); C8 (w64 TBL_bom);
    C8 (pe_s11 E); C8 (pe_s10 E); C8 (pe_s9 E); C8 (pe_s8 E); C8 (pe_s7 E); C8 (pe_s6 E); C8 (pe_s5 E);
    C8 (pe_s4 E); C8 (pe_s3 E); C8 (pe_s2 E); C8 (pe_s1 E); C8 (pe_s0 E); C8 (pe_ra E) ].

Lemma pframe_size : forall E j0 j8, cells_size (pframe E j0 j8) = 176%nat.
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
  | S_Match => x_v x Fmatch = TBL_attr_include
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

(* [comment removed for export] *)
Definition x_vio (x : pst) : option (vsb_rec * bool) := option_map (fun y => (y, true)) (x_vi x).

(* [comment removed for export] *)
Definition pw_bytes (vv : vsb_rec) (va vi : option vsb_rec) : Z :=
  40 + vb_size vv + match va with None => 0 | Some y => 40 + vb_size y end + match vi with None => 0 | Some y => 40 + vb_size y end.
Definition pw_nlive (va vi : option vsb_rec) : Z :=
  match va with None => 0 | Some _ => 2 end + match vi with None => 0 | Some _ => 2 end.
Lemma pw_bytes_world : forall vv va vi, world_bytes vv va (option_map (fun y => (y, true)) vi) = pw_bytes vv va vi.
Proof. intros vv [ya|] [yi|]; reflexivity. Qed.
Lemma pw_nlive_world : forall va vi, world_nlive va (option_map (fun y => (y, true)) vi) = pw_nlive va vi.
Proof. intros [ya|] [yi|]; reflexivity. Qed.
Lemma pw_nlive_range : forall va vi, 0 <= pw_nlive va vi <= 4.
Proof. intros [ya|] [yi|]; unfold pw_nlive; lia. Qed.

(* [comment removed for export] *)
Definition pzone (E : penv) (x : pst) (a : Z) : Prop :=
     blk (pe_VEP E) 312 a \/ (pe_S E <= a < pe_S E + 40) \/ blk (vb_buf (x_vv x)) (vb_size (x_vv x)) a
  \/ match x_va x with None => False | Some y => vsb_blocks (x_v x Fattr_vsb) y a end
  \/ match x_vi x with None => False | Some y => vsb_blocks (x_v x Finclude_src) y a end
  \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320).

(* [comment removed for export] *)
Definition oacost (x : pst) : Z := match x_va x with Some y => vb_len y + 8 | None => 0 end.
Definition oicost (x : pst) : Z := match x_vi x with Some y => vb_len y + 8 | None => 0 end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section INV.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  Definition va_world (E : penv) (x : pst) (A : AS) (m : mem) : Prop :=
    match x_va x with
    | None => x_v x Fattr_vsb = 0
    | Some y => x_v x Fattr_vsb <> 0 /\ vsb_obj LayoutP0 A m (x_v x Fattr_vsb) y false /\
                vb_size y <= vb_len y + 4096 /\   (* [comment removed for export] *)
                vsb_apart (x_v x Fattr_vsb) y [pe_VEP E; pe_wa E; pe_DATA E; pe_S E; vb_buf (x_vv x)]
    end.
  (* [comment removed for export] *)
  Definition vi_world (E : penv) (x : pst) (A : AS) (m : mem) : Prop :=
    match x_vi x with
    | None => x_v x Finclude_src = 0
    | Some y => x_v x Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (x_v x Finclude_src) y true /\ vb_error y = 0 /\
                vb_size y <= vb_len y + 4096 /\   (* [comment removed for export] *)
                vsb_apart (x_v x Finclude_src) y [pe_VEP E; pe_wa E; pe_DATA E; pe_S E; vb_buf (x_vv x)] /\
                match x_va x with None => True
                | Some z => vsb_apart (x_v x Finclude_src) y [x_v x Fattr_vsb; vb_buf z] end
    end.

  Record pinv (E : penv) (x : pst) (A : AS) (m : mem) : Prop := Build_pinv {
    (* [comment removed for export] *)
    pi_vep   : vep_obj LayoutP0 A m (pe_VEP E) (x_v x) (x_tag x) (x_q x);
    pi_base  : vep_base (pe_H E) (pe_VEP E) (x_v x);
    pi_flags : x_v x Fflags = pe_flags E;
    pi_vsbf  : x_v x Fvsb = pe_S E;
    pi_startup : x_v x Fstartup = 0;
    pi_state : x_v x Fstate = st0 (x_st x);
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
               x_v x Funtil <= x_v x Funtil_p <= x_v x Funtil + 2 /\ x_v x Funtil_s = (st0 S_NxtTag);
    pi_match : x_st x = S_Match ->
               x_v x Fmatch = TBL_bom \/ x_v x Fmatch = TBL_starttag \/ x_v x Fmatch = TBL_esi \/ x_v x Fmatch = TBL_attr_include;
    pi_dostuff : x_v x Fdostuff = 0 \/ x_v x Fdostuff = vi_do_include VI0 \/ x_v x Fdostuff = vi_do_remove VI0 \/
                 x_v x Fdostuff = vi_do_comment VI0;
    pi_armed : in_tag_cluster x -> x_v x Fdostuff <> 0;
    (* [comment removed for export] *)
    pi_attr  : x_v x Fattr = 0 \/
               (x_v x Fattr = TBL_attr_include /\ x_v x Fdostuff = vi_do_include VI0 /\
                (in_tag_cluster x \/ x_st x = S_TagError \/ x_st x = S_NxtTag \/ x_st x = S_MatchBuf));
    (* [comment removed for export] *)
    pi_attrst : attr_states x -> (x_st x = S_AttrGetValue \/ x_va x <> None) ->
                x_v x Fattr = TBL_attr_include /\
                (x_v x Fmatch_hit = TBL_attr_include \/ x_v x Fmatch_hit = TBL_attr_include + 16);
    pi_mattr : x_st x = S_Match -> x_v x Fmatch = TBL_attr_include -> x_v x Fattr = TBL_attr_include;
    (* [comment removed for export] *)
    pi_lookA : x_st x = S_Attr -> x_v x Fattr <> 0 -> x_p x < pe_e E -> vct_namestart (look E x) = true;
    pi_lookM : x_st x = S_Match -> x_v x Fmatch = TBL_attr_include -> x_p x < pe_e E -> vct_namestart (look E x) = true;
    (* [comment removed for export] *)
    pi_vsb   : vsb_obj LayoutP0 A m (pe_S E) (x_vv x) false;
    pi_room  : vb_size (x_vv x) <= vb_len (x_vv x) + 4096;   (* [comment removed for export] *)
    (* [comment removed for export] *)
    pi_out   : vb_len (x_vv x) + oacost x + oicost x + (match x_st x with S_AttrGetValue => 8 | _ => 0 end)
               <= 3 * x_v x Fo_last + 4 * (x_p x - pe_DATA E);
    pi_apart : vsb_apart (pe_S E) (x_vv x) [pe_VEP E; pe_wa E; pe_DATA E];
    (* [comment removed for export] *)
    pi_walive : a_live A (pe_wa E) = Some 40;
    (* [comment removed for export] *)
    pi_avsb  : x_v x Fattr_vsb <> 0 -> avsb_states x;
    pi_va    : va_world E x A m;
    (* [comment removed for export] *)
    pi_vi    : vi_world E x A m;
    (* [comment removed for export] *)
    pi_data  : data_obj LayoutP0 A m (pe_DATA E) (pe_inp E);
    pi_henv  : henv_ok LayoutP0 VI0 (pe_H E) m;
    pi_img   : img_ok0 m;
    pi_stk   : stk rsegs m (pe_lo E) (pe_sp E);
    pi_frame : exists j0 j8, rw_cells rsegs m (pe_sp E) (pframe E j0 j8);
    pi_mi    : mem_inv rsegs m;
    (* [comment removed for export] *)
    pi_lb    : a_livebytes A = pe_LB0 E - 56 + pw_bytes (x_vv x) (x_va x) (x_vi x);
    pi_nl    : a_nlive A = pe_NL0 E + pw_nlive (x_va x) (x_vi x)
  }.

  (* [comment removed for export] *)
  Definition hstep (E : penv) (x x' : pst) (A A' : AS) (m m' : mem) : Prop :=
       (forall p k, a_live A p = Some k -> ~ pst_blocks x p -> a_live A' p = Some k)
    /\ (forall p, pst_blocks x' p -> pst_blocks x p \/ a_live A p = None)
    /\ cframe LayoutP0 (owned A) (owned A') (h_sp (pe_H E)) PARSE_STACK (pzone E x) (parse_new (x_v x') (x_vv x') (x_va x')
                                                                                     (option_map (fun y => (y, true)) (x_vi x'))) m m'.
End INV.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rank (E : penv) (x : pst) : Z :=
  match x_st x with
  | S_Start | S_StartTag => 12
  | S_Match => if x_v x Fmatch =? TBL_attr_include then 3 else if x_v x Fmatch =? TBL_esi then 7 else 11
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
Definition loop_ms (E : penv) (pc p : Z) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (m : mem)
  : machine_state :=
  MS (mkR ra (Z_to_bv 64 (pe_sp E)) (pe_gp E) (al_tp LayoutP0) t0 t1 t2
          (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 (pe_e E)) (Z_to_bv 64 (st0 S_Start)) (Z_to_bv 64 (st0 S_BOM)) (Z_to_bv 64 VCT_ADDR) (Z_to_bv 64 (st0 S_TestXml))
          s7 (Z_to_bv 64 (st0 S_NxtTag)) (Z_to_bv 64 (st0 S_NotXml)) (Z_to_bv 64 (st0 S_NotMyTag)) (Z_to_bv 64 62) t3 t4 t5 t6)
     bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None m (seg_rom rsegs).

(* [comment removed for export] *)
Definition disp_pc (st : vstate) : Z :=
  match st with
  | S_Start => 0x1a188 | S_BOM => 0x1a1b8 | S_TestXml => 0x1a1e8 | S_NotXml => 0x1ab08 | S_NotMyTag => 0x1a21c
  | S_NxtTag => 0x1a244 | S_StartTag => 0x1a37c | S_Comment => 0x1a3d4 | S_CommentESI => 0x1a43c | S_CDATA => 0x1a4d8
  | S_end_ESITag => 0x1a4fc | S_ESITag => 0x1a50c | S_ESI_Include => 0x1a544 | S_ESI_Remove => 0x1a598
  | S_ESI_Comment => 0x1a5b0 | S_ESI_Bogon => 0x1a5f8 | S_InTag => 0x1a614 | S_TagError => 0x1a6a4 | S_Attr => 0x1a6cc
  | S_SkipAttribute => 0x1a7a8 | S_AttrGetValue => 0x1a818 | S_AttrDelim => 0x1a838 | S_AttrValue => 0x1a8c4
  | S_Match => 0x1a924 | S_MatchBuf => 0x1a99c | S_Until => 0x1a130
  end.
Definition disp_a1 (st : vstate) (verp : Z) : Z :=
  match st with
  | S_Start | S_BOM | S_TestXml | S_NotXml | S_NotMyTag | S_NxtTag => verp
  | S_StartTag => (st0 S_StartTag) | S_Comment => (st0 S_Comment) | S_CommentESI => (st0 S_CommentESI) | S_CDATA => (st0 S_CDATA)
  | S_end_ESITag | S_ESITag => (st0 S_ESITag)
  | S_ESI_Include => (st0 S_ESI_Include) | S_ESI_Remove => (st0 S_ESI_Remove) | S_ESI_Comment => (st0 S_ESI_Comment)
  | S_ESI_Bogon => (st0 S_ESI_Bogon) | S_InTag => 0x110bc | S_TagError => 0x110c8 (* [comment removed for export] *)
  | S_Attr => (st0 S_Attr) | S_SkipAttribute => (st0 S_SkipAttribute) | S_AttrGetValue => (st0 S_AttrGetValue)
  | S_AttrDelim => (st0 S_AttrDelim) | S_AttrValue => (st0 S_AttrValue) | S_Match => (st0 S_Match)
  | S_MatchBuf => (st0 S_MatchBuf) | S_Until => (st0 S_Until)
  end.
Definition disp_a2 (st : vstate) : option Z :=
  match st with
  | S_Start | S_BOM | S_TestXml | S_NotXml | S_NotMyTag | S_NxtTag | S_StartTag | S_Comment | S_CommentESI | S_CDATA => None
  | S_end_ESITag | S_ESITag | S_ESI_Include | S_ESI_Remove | S_ESI_Comment | S_ESI_Bogon | S_InTag => Some (st0 S_end_ESITag)
  | _ => Some (st0 S_TagError)
  end.
Definition disp_s7 (st : vstate) : option Z :=
  match st with
  | S_InTag | S_TagError | S_Attr | S_SkipAttribute | S_AttrGetValue | S_AttrDelim | S_AttrValue
  | S_Match | S_MatchBuf | S_Until => Some (st0 S_InTag)
  | _ => None
  end.
Definition oreg (o : option Z) (dflt : word) : word := match o with Some z => Z_to_bv 64 z | None => dflt end.

Definition head_ms (E : penv) (x : pst) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (m : mem) :=
  loop_ms E PC_HEAD (x_p x) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m.
Definition latch_ms (E : penv) (x : pst) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (m : mem) :=
  loop_ms E PC_LATCH (x_p x) ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m.
(* [comment removed for export] *)
Definition loop_msx (E : penv) (pc p : Z) (s4 : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (m : mem)
  : machine_state :=
  MS (mkR ra (Z_to_bv 64 (pe_sp E)) (pe_gp E) (al_tp LayoutP0) t0 t1 t2
          (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 p) a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 (pe_e E)) (Z_to_bv 64 (st0 S_Start)) s4 (Z_to_bv 64 VCT_ADDR) (Z_to_bv 64 (st0 S_TestXml))
          s7 (Z_to_bv 64 (st0 S_NxtTag)) (Z_to_bv 64 (st0 S_NotXml)) (Z_to_bv 64 (st0 S_NotMyTag)) (Z_to_bv 64 62) t3 t4 t5 t6)
     bvmap_empty (Z_to_bv 64 pc) (Z_to_bv 32 0) None m (seg_rom rsegs).
Definition exit_ms (E : penv) (x : pst) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 : word) (m : mem) :=
  loop_msx E PC_EXIT (x_p x) s4 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m.
(* [comment removed for export] *)
Definition disp_ms (E : penv) (x : pst) (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word) (m : mem) :=
  loop_ms E (disp_pc (x_st x)) (x_p x) ra t0 t1 t2 (Z_to_bv 64 (st0 (x_st x))) (Z_to_bv 64 (disp_a1 (x_st x) (x_v x Fver_p)))
          (oreg (disp_a2 (x_st x)) a2) a3 a4 a5 a6 a7 (oreg (disp_s7 (x_st x)) s7) t3 t4 t5 t6 m.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section H.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  (* [comment removed for export] *)
  Definition latch_K (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) : Prop :=
    forall (x' : pst) (A' : AS) (m' : mem) (md' : Model)
           (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      pinv E x' A' m' -> ainv A' m' md' -> md_frame md md' -> hstep E x x' A A' m m' ->
      (x_p x' < pe_e E -> phi E x' < phi E x /\ x_st x' <> S_MatchBuf) ->
      realizes rsegs (mkCfg (latch_ms E x' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m') md') T.

  (* [comment removed for export] *)
  Definition exit_K (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) : Prop :=
    forall (x' : pst) (A' : AS) (m' : mem) (md' : Model)
           (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 : word),
      pinv E x' A' m' -> ainv A' m' md' -> md_frame md md' -> hstep E x x' A A' m m' ->
      x_p x' = pe_e E ->
      realizes rsegs (mkCfg (exit_ms E x' ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 t3 t4 t5 t6 m') md') T.

  Definition handler_stmt (st : vstate) : Prop :=
    forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet)
           (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
      penv_ok E -> pinv E x A m -> ainv A m md -> x_st x = st -> x_p x < pe_e E ->
      latch_K E x A m md T -> exit_K E x A m md T ->
      realizes rsegs (mkCfg (disp_ms E x ra t0 t1 t2 a2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m) md) T.
End H.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HS.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Lemma hstep_refl : forall E x A m,
    mapped m (h_sp (pe_H E) - PARSE_STACK) PARSE_STACK ->
    hstep E x x A A m m.
  Proof.
    intros E x A m MAP. split; [|split].
    - intros p k Hp _. exact Hp.
    - intros p Hp. left; exact Hp.
    - split; [|split; [exact MAP|]].
      + intros a _ NO _ _ _ _. split; [reflexivity| exact NO].
      + intros a _ _ _ HN. right. left.
        unfold pzone. unfold parse_new in HN. cbn [option_map] in HN.
        destruct HN as [HN|[HN|HN]]; [right; right; left; exact HN| |].
        * right; right; right; left. destruct (x_va x); [exact HN| destruct HN].
        * right; right; right; right; left. destruct (x_vi x); [exact HN| destruct HN].
  Qed.
End HS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Cover.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.

  Definition vcover (H : henv) (A : AS) (excl : list Z) (V : Z -> Prop) : Prop :=
    forall a, V a -> (exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n)
                     \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  (* [comment removed for export] *)
  Definition hcover (A : AS) (excl : list Z) (V : Z -> Prop) : Prop :=
    forall a, V a -> exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n.

  Lemma hcover_vcover : forall H A excl V, hcover A excl V -> vcover H A excl V.
  Proof. intros H A excl V C a Ha. left. apply C, Ha. Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma cover_blk : forall (H : henv) A excl p n a,
    a_live A p = Some n -> ~ In p excl -> blk p n a ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof. intros H A excl p n a L NI [_ R]. left. exists p, n. auto. Qed.
  Lemma cover_rng : forall (H : henv) A excl p n a,
    a_live A p = Some n -> ~ In p excl -> p <= a < p + n ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof. intros H A excl p n a L NI R. left. exists p, n. auto. Qed.
  (* [comment removed for export] *)
  Lemma cover_vsc : forall (H : henv) A (excl : list Z) a,
    h_vsc H + 1304 <= a < h_vsc H + 1320 ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320).
  Proof. intros H A excl a R. right. exact R. Qed.
  Lemma hcover_blk : forall A excl p n a,
    a_live A p = Some n -> ~ In p excl -> blk p n a -> exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n.
  Proof. intros A excl p n a L NI [_ R]. exists p, n. auto. Qed.
  Lemma hcover_rng : forall A excl p n a,
    a_live A p = Some n -> ~ In p excl -> p <= a < p + n -> exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n.
  Proof. intros A excl p n a L NI R. exists p, n. auto. Qed.

  Variables (H : henv) (A A' : AS) (m m' : mem) (md : Model) (sp' win : Z) (V N : Z -> Prop) (excl : list Z).
  Hypothesis AINV : ainv A m md.
  Hypothesis CF : cframe LayoutP0 (owned A) (owned A') sp' win V N m m'.
  Hypothesis HG : henv_geom H.
  Hypothesis CEIL : alloc_ceiling <= sp' - win.
  Hypothesis WPOS : 0 <= win.
  Hypothesis SPH : sp' <= h_sp H.

  (* [comment removed for export] *)
  Lemma block_avoids : forall o0 k o n,
    vcover H A excl V -> In o0 excl -> a_live A o0 = Some k -> o0 <= o -> o + n <= o0 + k ->
    avoids_call sp' win V o n.
  Proof.
    intros o0 k o n C IN L H1 H2.
    (first [ pose proof ((live_geom LayoutP0 A m md o0 k AINV L)) as dR_1; dand5 dR_1 as K0 _ LO HI _ | destruct (live_geom LayoutP0 A m md o0 k AINV L) as (K0 & _ & LO & HI & _) ]).
    split; [left; lia|]. intros i Hi X.
    destruct (C _ X) as [(p & n' & Lp & NI & R)|R].
    - assert (NE : p <> o0) by (intros ->; exact (NI IN)).
      pose proof (as_live_disjoint A m md p n' o0 k AINV Lp L NE). lia.
    - destruct HG as (_ & G2 & _). unfold h_vsc in R. lia.
  Qed.

  Lemma rw_cells_call_blk : forall o0 k o cs,
    vcover H A excl V -> In o0 excl -> a_live A o0 = Some k ->
    o0 <= o -> o + Z.of_nat (cells_size cs) <= o0 + k ->
    rw_cells rsegs m o cs -> rw_cells rsegs m' o cs.
  Proof.
    intros o0 k o cs C IN L H1 H2 RC.
    eapply (rw_cells_ccall LayoutP0 A A' sp' win V N m m' CF); [| | exact RC].
    - eapply crange_block; [exact AINV| exact L| exact H1| exact H2| lia].
    - eapply block_avoids; eassumption.
  Qed.

  Lemma bytes_at_call_blk : forall o0 k o bs,
    vcover H A excl V -> In o0 excl -> a_live A o0 = Some k ->
    o0 <= o -> o + Z.of_nat (length bs) <= o0 + k ->
    bytes_at rsegs m o bs -> bytes_at rsegs m' o bs.
  Proof.
    intros o0 k o bs C IN L H1 H2 B.
    eapply (bytes_at_ccall LayoutP0 A A' sp' win V N m m' CF); [| | exact B].
    - eapply crange_block; [exact AINV| exact L| exact H1| exact H2| lia].
    - eapply block_avoids; eassumption.
  Qed.

  Lemma u8arr_call_blk : forall o0 k o bs,
    vcover H A excl V -> In o0 excl -> a_live A o0 = Some k ->
    o0 <= o -> o + Z.of_nat (length bs) <= o0 + k ->
    u8arr rsegs m o bs -> u8arr rsegs m' o bs.
  Proof.
    intros o0 k o bs C IN L H1 H2 B.
    eapply (u8arr_ccall LayoutP0 A A' sp' win V N m m' CF); [| | exact B].
    - eapply crange_block; [exact AINV| exact L| exact H1| exact H2| lia].
    - eapply block_avoids; eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma rw_cells_call_stack : forall a cs,
    vcover H A excl V -> rw_cells rsegs m a cs -> sp' <= a -> a + Z.of_nat (cells_size cs) <= h_vsc H + 1304 ->
    rw_cells rsegs m' a cs.
  Proof.
    intros a cs C RC LO HI.
    eapply (rw_cells_ccall_stack LayoutP0 A A' m md m' sp' win V N); [exact AINV| exact CF| exact RC| lia| right; exact LO|].
    intros y Hy X. destruct (C _ X) as [(p & n' & Lp & _ & R)|R]; [|lia].
    (first [ pose proof ((live_geom LayoutP0 A m md p n' AINV Lp)) as dR_2; dand5 dR_2 as _ _ _ PHI _ | destruct (live_geom LayoutP0 A m md p n' AINV Lp) as (_ & _ & _ & PHI & _) ]). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma img_call : vcover H A excl V -> img_ok0 m -> img_ok0 m'.
  Proof.
    intros C IMG. pose proof alloc_ceiling_val as CV. destruct HG as (G1 & G2 & G3).
    eapply (img_ok0_ccall A A' m md m' sp' win V N AINV CF); [unfold IMG0_HI; lia| | exact IMG].
    intros a Ha X. unfold IMG0_LO, IMG0_HI in Ha. destruct (C _ X) as [(p & n' & Lp & _ & R)|R]; [| unfold h_vsc in R; lia].
    (first [ pose proof ((live_geom LayoutP0 A m md p n' AINV Lp)) as dR_3; dand6 dR_3 as _ _ _ _ OFF _ | destruct (live_geom LayoutP0 A m md p n' AINV Lp) as (_ & _ & _ & _ & OFF & _) ]). unfold off_image in OFF. cbn in OFF. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hobj_call : vcover H A excl V -> hobj_ok LayoutP0 VI0 H m -> hobj_ok LayoutP0 VI0 H m'.
  Proof.
    intros C HO. destruct HG as (G1 & G2 & G3).
    eapply (hobj_ok_ccall LayoutP0 VI0 H A A' m md m' sp' win V N AINV CF (conj G1 (conj G2 G3)) HO SPH).
    intros a Ha X. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha.
    destruct (C _ X) as [(p & n' & Lp & _ & R)|R]; [| unfold h_vsc in R; lia].
    (first [ pose proof ((live_geom LayoutP0 A m md p n' AINV Lp)) as dR_4; dand5 dR_4 as _ _ _ PHI _ | destruct (live_geom LayoutP0 A m md p n' AINV Lp) as (_ & _ & _ & PHI & _) ]). lia.
  Qed.

  Lemma glob_call : hcover A excl V -> glob_ok LayoutP0 VI0 H m -> glob_ok LayoutP0 VI0 H m'.
  Proof.
    intros C GL. destruct HG as (G1 & G2 & G3). pose proof GL as (E & _). cbn [vi_bss VI0] in E.
    eapply (glob_ok_ccall LayoutP0 VI0 H A A' m md m' sp' win V N AINV CF (conj G1 (conj G2 G3)) GL SPH CEIL).
    - rewrite E. cbn. lia.
    - rewrite E. cbn. lia.
    - intros i Hi. rewrite E. cbn. unfold p0_static. lia.
    - rewrite E. change (al_errno LayoutP0) with 0x420b4. lia.
    - intros a Ha X. unfold h_cp, h_vsc in Ha. rewrite E in Ha.
      (first [ pose proof ((C _ X)) as dR_5; dex2 dR_5 as p n'; dand3 dR_5 as Lp _ R | pose proof ((C _ X)) as dR_5; dand5 dR_5 as p n' Lp _ R | destruct (C _ X) as (p & n' & Lp & _ & R) ]).
      (first [ pose proof ((live_geom LayoutP0 A m md p n' AINV Lp)) as dR_6; dand6 dR_6 as _ _ _ PHI OFF _ | destruct (live_geom LayoutP0 A m md p n' AINV Lp) as (_ & _ & _ & PHI & OFF & _) ]). unfold off_image in OFF. cbn in OFF.
      pose proof alloc_ceiling_val. lia.
  Qed.

  Lemma henv_call : hcover A excl V -> henv_ok LayoutP0 VI0 H m -> henv_ok LayoutP0 VI0 H m'.
  Proof. intros C [GL HO]. split; [apply glob_call; assumption| apply hobj_call; [apply hcover_vcover; exact C| exact HO]]. Qed.

  (* [comment removed for export] *)
  Lemma vsb_obj_call : forall S v fin,
    vcover H A excl V -> In S excl -> In (vb_buf v) excl ->
    a_live A' S = Some 40 -> a_live A' (vb_buf v) = Some (vb_size v) ->
    vsb_obj LayoutP0 A m S v fin -> vsb_obj LayoutP0 A' m' S v fin.
  Proof.
    (intros S v fin C I1 I2 L1' L2'; (first [ intro dR_7; dand6 dR_7 as VC VI LS LB NE (bs & U & LEN & NUL) | intros (VC & VI & LS & LB & NE & (bs & U & LEN & NUL)) ])).
    split; [|split; [exact VI|]; split; [exact L1'|]; split; [exact L2'|]; split; [exact NE|]].
    - eapply (rw_cells_call_blk S 40); [exact C| exact I1| exact LS| lia| rewrite vsb_cells_size; lia| exact VC].
    - exists bs. split; [|split; [exact LEN| exact NUL]].
      eapply (u8arr_call_blk (vb_buf v) (vb_size v)); [exact C| exact I2| exact LB| lia| lia| exact U].
  Qed.

  Lemma vep_obj_call : forall VEP v tag q,
    vcover H A excl V -> In VEP excl -> a_live A' VEP = Some 312 ->
    vep_obj LayoutP0 A m VEP v tag q -> vep_obj LayoutP0 A' m' VEP v tag q.
  Proof.
    (intros VEP v tag q C IN L'; (first [ intro dR_8; dand4 dR_8 as L RC LT WF | intros (L & RC & LT & WF) ])).
    split; [exact L'|]. split; [|split; [exact LT| exact WF]].
    eapply (rw_cells_call_blk VEP 312); [exact C| exact IN| exact L| lia| rewrite vep_cells_size by assumption; lia| exact RC].
  Qed.

  Lemma data_obj_call : forall DATA inp,
    vcover H A excl V -> In DATA excl -> a_live A' DATA = Some (Z.of_nat (length inp)) ->
    data_obj LayoutP0 A m DATA inp -> data_obj LayoutP0 A' m' DATA inp.
  Proof.
    (intros DATA inp C IN L'; (first [ intro dR_9; dand3 dR_9 as L B LEN | intros (L & B & LEN) ])).
    split; [exact L'|]. split; [|exact LEN].
    eapply (bytes_at_call_blk DATA (Z.of_nat (length inp))); [exact C| exact IN| exact L| lia| lia| exact B].
  Qed.
End Cover.

(* [comment removed for export] *)
Section FrameCall.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Lemma pframe_call : forall E A A' m m' md sp' win V N excl j0 j8,
    penv_ok E -> ainv A m md -> cframe LayoutP0 (owned A) (owned A') sp' win V N m m' ->
    alloc_ceiling <= sp' - win -> 0 <= win -> sp' <= pe_sp E ->
    vcover (pe_H E) A excl V ->
    rw_cells rsegs m (pe_sp E) (pframe E j0 j8) -> rw_cells rsegs m' (pe_sp E) (pframe E j0 j8).
  Proof.
    intros E A A' m m' md sp' win V N excl j0 j8 PE AINV CF CEIL WPOS SP C FR.
    destruct PE as (HG & _). pose proof HG as (G1 & G2 & G3).
    eapply (rw_cells_call_stack (pe_H E) A A' m m' md sp' win V N excl); try eassumption.
    all: rewrite ?pframe_size; unfold pe_sp, h_vsc in *; lia.
  Qed.
End FrameCall.

(* [comment removed for export] *)
Ltac open_pinv PI :=
  destruct PI as [VEPO BASE FLG VSBF STUP STATE CNT VERP PLE B01 TAGI DELIM ESIC UNTL MTCH DOST ARMED ATTR ATTRST
                  MATTR LOOKA LOOKM VSBO ROOM OUT APART WAL AVSB VA VI DATA HENV IMG STK FRAME MI LB NL].
