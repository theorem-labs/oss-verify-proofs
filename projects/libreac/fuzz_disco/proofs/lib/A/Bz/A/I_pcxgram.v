(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_pcxgram.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by reloc.py (target disco-A): module paths changed; 0 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table: this file's rows in provenance/evidence/g9-gxa/g9tool/g9-table-disco-A.tsv). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_manifest.asan from a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/A/I_pcxgram.v: module paths and 0 address numerals by alreloc 7a60a01f65f446d8, each paired by object; the decided numerals are listed in the commit body. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith List Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* parg: the printf argument kinds, from openssl/ct lib/Spec/PrintfModel.v:37 (hub 60b8c89d30), unchanged. *)
Inductive parg : Type := PA_s (s : list Z) | PA_sn | PA_i (i : Z) | PA_u (u : Z) | PA_z (u : Z) | PA_g (d : Z).

(* The pcx grammar of printf_common's list walk (I_pcxlist.v): from openssl/ct lib/CtB/I_vsnstmt.v:24-147
   (hub 60b8c89d30), unchanged; the vsnprintf statements of that file and their imports are not ported. *)
Inductive pcx_kind : Type := PK_int | PK_long | PK_char | PK_str.
Inductive pcx_prec : Type := PP_none | PP_num | PP_star.

Definition pcx_isdigit (c : Z) : bool := (48 <=? c) && (c <=? 57).
Definition pcx_isflag (c : Z) : bool := (c =? 45) || (c =? 48).

Fixpoint pcx_flags (s : list Z) : list Z :=
  match s with c :: s' => if pcx_isflag c then pcx_flags s' else s | [] => [] end.
Fixpoint pcx_digits (s : list Z) : list Z :=
  match s with c :: s' => if pcx_isdigit c then pcx_digits s' else s | [] => [] end.

Definition pcx_conv (lm : bool) (c : Z) : option pcx_kind :=
  if (c =? 100) || (c =? 105) || (c =? 117) || (c =? 120) || (c =? 88) then Some (if lm then PK_long else PK_int)
  else if lm then None
  else if c =? 99 then Some PK_char
  else if c =? 115 then Some PK_str
  else None.

(* [comment removed for export] *)
Definition pcx_precp (s : list Z) : option (pcx_prec * list Z) :=
  match s with
  | 46 :: 42 :: s' => match s' with c :: _ => if pcx_isdigit c then None else Some (PP_star, s') | [] => None end
  | 46 :: s' => match s' with c :: _ => if pcx_isdigit c then Some (PP_num, pcx_digits s') else None | [] => None end
  | _ => Some (PP_none, s)
  end.

Definition pcx_lmp (s3 : list Z) : bool * list Z :=
  match s3 with
  | a :: s' => if a =? 108 then match s' with b :: s'' => if b =? 108 then (true, s'') else (true, s') | [] => (true, s') end
               else if a =? 122 then (true, s')
               else (false, s3)
  | [] => (false, s3)
  end.

Lemma pcx_lmp_inv : forall s3 lm s4, pcx_lmp s3 = (lm, s4) ->
  exists ll, s3 = ll ++ s4 /\
    ((lm = false /\ ll = []) \/ (lm = true /\ (ll = [108] \/ ll = [108; 108] \/ ll = [122]))).
Proof.
  intros s3 lm s4 H. unfold pcx_lmp in H. destruct s3 as [|a s'].
  - injection H as <- <-. exists []. split; [reflexivity|]. left; split; reflexivity.
  - destruct (Z.eqb_spec a 108) as [->|N108].
    + destruct s' as [|b s''].
      * injection H as <- <-. exists [108]. split; [reflexivity|]. right; split; [reflexivity| left; reflexivity].
      * destruct (Z.eqb_spec b 108) as [->|N108b].
        -- injection H as <- <-. exists [108; 108]. split; [reflexivity|]. right; split; [reflexivity| right; left; reflexivity].
        -- injection H as <- <-. exists [108]. split; [reflexivity|]. right; split; [reflexivity| left; reflexivity].
    + destruct (Z.eqb_spec a 122) as [->|N122].
      * injection H as <- <-. exists [122]. split; [reflexivity|]. right; split; [reflexivity| right; right; reflexivity].
      * injection H as <- <-. exists []. split; [reflexivity|]. left; split; reflexivity.
Qed.

(* [comment removed for export] *)
Definition pcx_dir (s : list Z) : option (bool * pcx_prec * pcx_kind * list Z) :=
  let s1 := pcx_flags s in
  let '(ws, s2) := match s1 with 42 :: s' => (true, s') | _ => (false, pcx_digits s1) end in
  match pcx_precp s2 with
  | None => None
  | Some (pp, s3) =>
      let '(lm, s4) := pcx_lmp s3 in
      match s4 with
      | c :: s5 => match pcx_conv lm c with
                   | Some k => match pp, k with PP_none, _ => Some (ws, pp, k, s5) | _, PK_str => Some (ws, pp, k, s5) | _, _ => None end
                   | None => None
                   end
      | [] => None
      end
  end.

(* [comment removed for export] *)
Definition pcx_fits (k : pcx_kind) (a : parg) : bool :=
  match k, a with
  | PK_str, PA_s _ => true | PK_str, PA_sn => true | PK_str, _ => false
  | _, PA_s _ => false | _, PA_sn => false | _, _ => true
  end.

(* [comment removed for export] *)
Fixpoint pcx_walk (fuel : nat) (s : list Z) (args : list parg) : option nat :=
  match fuel with
  | O => None
  | S fuel' =>
      match s with
      | [] => None
      | c :: s' =>
          if c =? 0 then Some 0%nat
          else if c =? 37 then
            match pcx_dir s' with
            | None => None
            | Some (ws, pp, k, rest) =>
                match (if ws then match args with _ :: t => Some t | [] => None end else Some args) with
                | None => None
                | Some args1 =>
                    match (match pp with PP_star => match args1 with _ :: t => Some t | [] => None end | _ => Some args1 end) with
                    | None => None
                    | Some args2 =>
                        match args2 with
                        | a :: args3 =>
                            if pcx_fits k a then
                              match pcx_walk fuel' rest args3 with
                              | Some n => Some ((if ws then 1 else 0) + (match pp with PP_star => 1 | _ => 0 end) + 1 + n)%nat
                              | None => None
                              end
                            else None
                        | [] => None
                        end
                    end
                end
            end
          else if (0 <? c) && (c <? 256) then pcx_walk fuel' s' args
          else None
      end
  end.

Definition pcomx_ok (fmt : list Z) (args : list parg) : bool :=
  match pcx_walk (length fmt) fmt args with Some _ => true | None => false end.

(* [comment removed for export] *)
Definition vhd_cov (covs : list (option Z)) : option Z := match covs with [] => None | c :: _ => c end.
Fixpoint pcx_covs (fuel : nat) (s : list Z) (args : list parg) (covs : list (option Z)) : list (option Z) :=
  match fuel with
  | O => []
  | S fuel' =>
      match s with
      | [] => []
      | c :: s' =>
          if c =? 0 then []
          else if c =? 37 then
            match pcx_dir s' with
            | None => []
            | Some (ws, pp, k, rest) =>
                match (if ws then match args with _ :: t => Some (t, tl covs) | [] => None end else Some (args, covs)) with
                | None => []
                | Some (args1, covs1) =>
                    match (match pp with PP_star => match args1 with _ :: t => Some (t, tl covs1) | [] => None end | _ => Some (args1, covs1) end) with
                    | None => []
                    | Some (args2, covs2) =>
                        match args2 with
                        | a :: args3 =>
                            (if ws then [None] else []) ++ (match pp with PP_star => [None] | _ => [] end)
                            ++ (match pp, k with PP_star, PK_str => vhd_cov covs2 | _, _ => None end)
                            :: pcx_covs fuel' rest args3 (tl covs2)
                        | [] => []
                        end
                    end
                end
            end
          else if (0 <? c) && (c <? 256) then pcx_covs fuel' s' args covs
          else []
      end
  end.
