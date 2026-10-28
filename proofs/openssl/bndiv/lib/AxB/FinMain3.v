(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon Require Import FastWord.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie AxLazy AxLin AxVal AxBytes AxMem AxState AxSys.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxA Require Import AxExportQ. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.AxB Require Import AxExportS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section Forms.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition ld_form (B : AST) (f : lin) : option lin :=
  match a_load segs (a_mem B) (XS (snd f) (wofZ (fst f))) 8 with
  | Some l => match val_of_bytes (a_facts B) SZ8 false l with
              | XL w => Some (wZ w, [])
              | XS ts o => Some (wZ o, ts)
              | _ => None
              end
  | None => None
  end.

Definition ld_lit (B : AST) (a : Z) : option Z :=
  match ld_form B (a, []) with Some (c, []) => Some c | _ => None end.

(* [comment removed for export] *)
Record pcells : Type := PCells {
  pc_PRB : Z; pc_SB : Z; pc_PAB : Z; pc_TCX : Z; pc_T_off : Z; pc_top_off : Z; pc_FSB : Z; pc_DTV : Z; pc_DNB : Z; pc_SSB : Z; pc_f0 : Z
}.

Definition entry_form (B : AST) : option lin :=
  match List.filter is_entry (a_mem B) with R :: _ => Some (wZ (rg_bo R), rg_ts R) | [] => None end.

Definition bf_of (P : pcells) (B : AST) : option bforms :=
  match entry_form B, ld_form B (pc_PRB P, []), ld_form B (pc_SB P, []), ld_form B (pc_PAB P, []), ld_form B (pc_TCX P, []) with
  | Some fsp, Some fPRB, Some fSB, Some fPAB, Some fTCX =>
      match ld_form B (laddc fTCX (pc_T_off P)) with
      | Some fT =>
          match ld_form B (laddc fT (pc_top_off P)), ld_form B (pc_FSB P, []), ld_form B (pc_DTV P, []), ld_form B (pc_DNB P, []),
                ld_form B (pc_SSB P, []), ld_lit B (pc_f0 P), am_tid (a_model B) with
          | Some ftop, Some fFSB, Some fDTV, Some fDNB, Some fSSB, Some f0, Some (XS tts to) =>
              Some (BForms fsp ftop fPRB fSB fPAB fT fTCX fDTV fFSB fDNB fSSB f0 (wZ to, tts))
          | _, _, _, _, _, _, _ => None
          end
      | None => None
      end
  | _, _, _, _, _ => None
  end.

End Forms.

(* [comment removed for export] *)
Definition PCELLS_A : pcells :=
  PCells 0x6a0398 0x6a03b8 0x6a03e0 0xbfc1f8 0x98 8 0xbdae50 0xbdae68 0xb858e8 0x7758d8 0x7758c8.
