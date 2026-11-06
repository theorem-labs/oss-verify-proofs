(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst FxEnt FxFrame FxCall FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxCallNode FxBDec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQSites AsanQcsNode.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxCallNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxBDec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr.FxQcsChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSites OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxRebyte HxRecell.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXHB Require Import HxPay HxFmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import M4Pure HxSurg HxDerive HxListNodes HxLow HxVConst HxDecN HxRepl1 HxPsrK HxQsMemset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive hnode : Type :=
| HPAF | HPC1 | HPC2 | HPLD      (* [comment removed for export] *)
| HSITE (s : m4site)             (* [comment removed for export] *)
| HREB (k : Z) (n : nat)         (* [comment removed for export] *)
| HSITEF (j : nat) (keep qk : list positive) (f : sst -> list (vop * Z * rkind))   (* [comment removed for export] *)
| HSURG (h : surg)               (* [comment removed for export] *)
| HZRT (f : sst -> option (nat * Z * nat))   (* [comment removed for export] *)
| HZBK (f : sst -> option (nat * Z * nat))   (* [comment removed for export] *)
| HRB1 (f : sst -> option (nat * Z))         (* [comment removed for export] *)
| HRBK (f : sst -> option (nat * Z * nat))   (* [comment removed for export] *)
| HSCL (f : sst -> option (lin * Z))         (* [comment removed for export] *)
| HFMT                                       (* [comment removed for export] *)
| HDEC (f : sst -> option (nat * Z * Z))     (* [comment removed for export] *)
| HTRK (f : sst -> option (nat * Z))         (* [comment removed for export] *)
| HREPL (f : sst -> option (nat * Z * lin))  (* [comment removed for export] *)
| HUNZ (f : sst -> option nat)               (* [comment removed for export] *)
| HLOWB (f : sst -> option lin)              (* [comment removed for export] *)
| HPROMZ (f : sst -> option nat)             (* [comment removed for export] *)
| HTRY (h : hnode)                           (* [comment removed for export] *)
| HSUBS (f : sst -> list fact)               (* [comment removed for export] *)
| HIXF (f : sst -> option lin)               (* [comment removed for export] *)
| HPSR (f : sst -> option lin)               (* [comment removed for export] *)
| HLOWBITS (f : sst -> option (positive * Z)) (* [comment removed for export] *)
| HVCONST (f : sst -> option positive)       (* [comment removed for export] *)
| HNAMER (f : sst -> option positive)        (* [comment removed for export] *)
| HFSUM (f : sst -> option (lin * lin))       (* [comment removed for export] *)
| HDECV (f : sst -> option (positive * Z))  (* [comment removed for export] *)
| HDECN (f : sst -> option (positive * Z * Z))   (* [comment removed for export] *)
| HNAMEL (f : sst -> option lin)               (* [comment removed for export] *)
| HREPL1 (f : sst -> option (nat * Z * lin))   (* [comment removed for export] *)
| HPSRK (k : positive) (f : sst -> option lin)   (* [comment removed for export] *)
| HQSM                                           (* [comment removed for export] *)
| HIXFL (f : sst -> list lin)                    (* [comment removed for export] *)
| HFSUML (f : sst -> list (lin * lin))          (* [comment removed for export] *)
| HPL1.                                         (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint find_idxh (rgs : list region) (a : lin) (i : nat) : option (nat * Z) :=
  match rgs with
  | [] => None
  | R :: rs => match is_const (lsub a (rg_base R)) with
               | Some o => if (Z.leb 0 o && match is_const (rg_size R) with Some n => Z.ltb o n | None => true end)%bool then Some (i, o)
                           else find_idxh rs a (S i)
               | None => find_idxh rs a (S i)
               end
  end.
Definition hreb (k : Z) (n : nat) (S : sst) : option sst :=
  match find_idxh (s_rgs S) (rget (s_regs S) (rkz k)) 0 with Some (i, o) => hx_rebz i o n S | None => None end.

Section H.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Hypothesis Hwx : wx_segs_nowrap AsanUbsan.M.loaded_segments.
Variable g : pgeo.
Variable cons : list m4con.
Hypothesis Hcons : Forall (con_ok AsanUbsan.M.loaded_segments) cons.
Variable img : tree Z.
Hypothesis Himg : img_ok AsanUbsan.M.loaded_segments img.

Fixpoint ppostH (h : hnode) (S : sst) (M : smodel) : option sst :=
  match h with
  | HPAF => H_PAF g S
  | HPC1 => H_PC1 g S
  | HPC2 => H_PC2 g S
  | HPLD => H_PLD g S
  | HSITE s => ppostM cons s S M
  | HREB k n => hreb k n S
  | HSITEF j keep qk f => ppostM cons (j, keep, qk, f S) S M
  | HSURG h => surg_post h S
  | HZRT f => match f S with Some (i, o, n) => hx_rebzr i o n S | None => None end
  | HZBK f => match f S with Some (i, o, n) => hx_zbk i o n S | None => None end
  | HRB1 f => match f S with Some (i, o) => hx_reb1 i o S | None => None end
  | HRBK f => match f S with Some (i, o, n) => hx_rebk i o n S | None => None end
  | HSCL f => match f S with Some (l, s) => hx_scale l s S | None => None end
  | HFMT => H_FMT S
  | HDEC f => match f S with Some (i, o, k) => hx_dec i o k S | None => None end
  | HTRK f => match f S with Some (i, o) => hx_trk i o S | None => None end
  | HREPL f => match f S with Some (i, o, l) => hx_repl i o l S | None => None end
  | HUNZ f => match f S with Some i => hx_unz i S | None => None end
  | HLOWB f => match f S with Some b => lowb_post S M b | None => None end
  | HPROMZ f => match f S with Some i => hx_promz i S | None => None end
  | HTRY h' => match ppostH h' S M with Some K => Some K | None => Some S end
  | HSUBS f => Some (hx_subfs (f S) S)
  | HIXF f => match f S with Some l => hx_ixf l S | None => None end
  | HPSR f => match f S with Some l => hx_psr l S | None => None end
  | HLOWBITS f => match f S with Some (y, k) => hx_lowbits y k S | None => None end
  | HVCONST f => match f S with Some v => vconst_post S M v | None => None end
  | HNAMER f => match f S with Some k => hx_namer k S | None => None end
  | HFSUM f => match f S with Some (l1, l2) => hx_fsum l1 l2 S | None => None end
  | HDECV f => match f S with Some (v, k) => dec_post S M v k | None => None end
  | HDECN f => match f S with Some (v, c, k) => decn_post S M v c k | None => None end
  | HNAMEL f => match f S with Some l => hx_namel l S | None => None end
  | HREPL1 f => match f S with Some (i, o, l) => hx_repl1 i o l S | None => None end
  | HPSRK k f => match f S with Some l => hx_psrk k l S | None => None end
  | HQSM => if qcs_chk img QSS_MEMSET S M then Some (qcs_post QSS_MEMSET S) else None
  | HIXFL f => hx_ixfl (f S) S
  | HFSUML f => hx_fsuml (f S) S
  | HPL1 => H_PL1 g S
  end.

#[using="Hcons"] Lemma ppostH_rule : forall h S M K, ppostH h S M = Some K -> (match h with HSURG _ | HLOWB _ | HTRY _ | HVCONST _ | HDECV _ | HDECN _ | HQSM => False | _ => True end) ->
  call_rule AsanUbsan.M.loaded_segments S K /\ (s_next S <= s_next K)%positive /\ shape (s_rgs K) = shape (s_rgs S).
Proof. LiaFast.lf_pins (fun (Hcons : LiaFast.U) => LiaFast.u0).
  intros h S M K Hp Hh. destruct h as [| | | |s|k n|j keep qk f|sh|f|f|f|f|f| |f|f|f|f|f|f|h'|f|f|f|f|f|f|f|f|f|f|f|kk f| |f|f|]; cbn [ppostH] in Hp.
  - exact (H_PAF_ok g S K Hp).
  - exact (H_PC1_ok g S K Hp).
  - exact (H_PC2_ok g S K Hp).
  - exact (H_PLD_ok g S K Hp).
  - exact (ppostM_ok _ cons Hcons s S M K Hp).
  - unfold hreb in Hp. destruct (find_idxh (s_rgs S) (rget (s_regs S) (rkz k)) 0) as [[i o]|]; [|discriminate].
    exact (hx_rebz_ok AsanUbsan.M.loaded_segments i o n S K Hp).
  - exact (ppostM_ok _ cons Hcons (j, keep, qk, f S) S M K Hp).
  - destruct Hh.
  - destruct (f S) as [[[i o] n]|]; [|discriminate]. exact (hx_rebzr_ok AsanUbsan.M.loaded_segments i o n S K Hp).
  - destruct (f S) as [[[i o] n]|]; [|discriminate]. exact (hx_zbk_ok AsanUbsan.M.loaded_segments i o n S K Hp).
  - destruct (f S) as [[i o]|]; [|discriminate]. exact (hx_reb1_ok AsanUbsan.M.loaded_segments i o S K Hp).
  - destruct (f S) as [[[i o] n]|]; [|discriminate]. exact (hx_rebk_ok AsanUbsan.M.loaded_segments i o n S K Hp).
  - destruct (f S) as [[l sc]|]; [|discriminate]. exact (hx_scale_ok AsanUbsan.M.loaded_segments l sc S K Hp).
  - exact (H_FMT_ok S K Hp).
  - destruct (f S) as [[[i o] k]|]; [|discriminate]. exact (hx_dec_ok AsanUbsan.M.loaded_segments i o k S K Hp).
  - destruct (f S) as [[i o]|]; [|discriminate]. exact (hx_trk_ok AsanUbsan.M.loaded_segments i o S K Hp).
  - destruct (f S) as [[[i o] l]|]; [|discriminate]. exact (hx_repl_ok AsanUbsan.M.loaded_segments i o l S K Hp).
  - destruct (f S) as [i|]; [|discriminate]. exact (hx_unz_ok AsanUbsan.M.loaded_segments i S K Hp).
  - destruct Hh.
  - destruct (f S) as [i|]; [|discriminate]. exact (hx_promz_ok AsanUbsan.M.loaded_segments i S K Hp).
  - destruct Hh.
  - injection Hp as <-. exact (hx_subfs_ok AsanUbsan.M.loaded_segments (f S) S).
  - destruct (f S) as [l|]; [|discriminate]. exact (hx_ixf_ok AsanUbsan.M.loaded_segments l S K Hp).
  - destruct (f S) as [l|]; [|discriminate]. exact (hx_psr_ok AsanUbsan.M.loaded_segments l S K Hp).
  - destruct (f S) as [[y k]|]; [|discriminate]. exact (hx_lowbits_ok AsanUbsan.M.loaded_segments y k S K Hp).
  - destruct Hh.
  - destruct (f S) as [k0|]; [|discriminate]. exact (hx_namer_ok AsanUbsan.M.loaded_segments k0 S K Hp).
  - destruct (f S) as [[l1 l2]|]; [|discriminate]. exact (hx_fsum_ok AsanUbsan.M.loaded_segments l1 l2 S K Hp).
  - destruct Hh.
  - destruct Hh.
  - destruct (f S) as [l|]; [|discriminate]. exact (hx_namel_ok AsanUbsan.M.loaded_segments l S K Hp).
  - destruct (f S) as [[[i o] l]|]; [|discriminate]. exact (hx_repl1_ok AsanUbsan.M.loaded_segments i o l S K Hp).
  - destruct (f S) as [l|]; [|discriminate]. exact (hx_psrk_ok AsanUbsan.M.loaded_segments kk l S K Hp).
  - destruct Hh.
  - exact (hx_ixfl_ok AsanUbsan.M.loaded_segments (f S) S K Hp).
  - exact (hx_fsuml_ok AsanUbsan.M.loaded_segments (f S) S K Hp).
  - exact (H_PL1_ok g S K Hp).
Qed.

#[using="Hwx Hcons Himg"] Theorem pnodeH_ok : forall h, pnode_ok AsanUbsan.M.loaded_segments cfg LIMIT ppostH h.
Proof. LiaFast.lf_pins (fun (Hwx Hcons Himg : LiaFast.U) => LiaFast.u0).
  intros h. induction h as [| | | |s|k n|j keep qk f|sh|f|f|f|f|f| |f|f|f|f|f|f|h' IH|f|f|f|f|f|f|f|f|f|f|f|kk f| |f|f|]; intros S M S' Hp model0 mem0 E ms model T Hd Hk.
  34: { cbn [ppostH] in Hp. destruct (qcs_chk img QSS_MEMSET S M) eqn:Hc; [|discriminate]. injection Hp as <-.
        exact (den_qcs cfg LIMIT model0 mem0 img Hwx Himg QSS_MEMSET S M E ms model T QSS_MEMSET_ok Hc Hd Hk). }
  30: { cbn [ppostH] in Hp. destruct (f S) as [[[v c] k]|]; [|discriminate].
        exact (den_decn AsanUbsan.M.loaded_segments cfg LIMIT model0 mem0 S M v c k S' Hp E ms model T Hd Hk). }
  29: { cbn [ppostH] in Hp. destruct (f S) as [[v k]|]; [|discriminate].
        exact (den_dec AsanUbsan.M.loaded_segments cfg LIMIT model0 mem0 S M v k S' Hp E ms model T Hd Hk). }
  26: { cbn [ppostH] in Hp. destruct (f S) as [v|]; [|discriminate].
        exact (Hk E ms model (agree_refl _ _) (den_vconst AsanUbsan.M.loaded_segments LIMIT model0 mem0 S M v S' E ms model Hp Hd)). }
  21: { cbn [ppostH] in Hp. destruct (ppostH h' S M) as [K|] eqn:Hi.
        - injection Hp as <-. exact (IH S M K Hi model0 mem0 E ms model T Hd Hk).
        - injection Hp as <-. exact (Hk E ms model (agree_refl _ _) Hd). }
  19: { cbn [ppostH] in Hp. destruct (f S) as [b|]; [|discriminate].
        exact (Hk E ms model (agree_refl _ _) (den_lowb AsanUbsan.M.loaded_segments LIMIT model0 mem0 E S M ms model b S' Hd Hp)). }
  8: { cbn [ppostH] in Hp. destruct (surg_den LIMIT model0 mem0 sh E S M ms model S' Hd Hp) as [Hd' _].
       exact (Hk E ms model (agree_refl _ _) Hd'). }
  all: destruct (ppostH_rule _ S M S' Hp I) as (Hr & Hn & Hsh);
       exact (den_call_gen AsanUbsan.M.loaded_segments cfg LIMIT Hwx model0 mem0 E S M ms model T S' Hd Hr Hn Hsh Hk).
Qed.
End H.
(* [comment removed for export] *)
