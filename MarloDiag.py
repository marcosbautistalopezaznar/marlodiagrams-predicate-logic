from flask import Flask, render_template, request
import re
from collections import Counter
import matplotlib.pyplot as plt
import matplotlib.patches as patches
import numpy as np

app = Flask(__name__)


def validate_input(subject, in_predicates, out_predicates):
    if not re.match(r"^([a-zA-Z¬]+/)*[a-zA-Z¬]+$", subject):
        return False, "Invalid subject. Only literals, their negation, and disjunction '/' are allowed. '/' must be preceded and followed by at least one literal or its negation."

    predicates = in_predicates.split(',')
    for predicate in predicates:
        if not re.match(r"^([a-zA-Z¬]+/)*[a-zA-Z¬]+$", predicate.strip()) and predicate.strip() != "?":
            return False, "Invalid input predicates. Only literals, their negation, disjunction '/', and '?' are allowed. '/' must be preceded and followed by at least one literal or its negation."

    if not out_predicates:  # Si la entrada está vacía, retornamos True
        return True, ""
        predicates = out_predicates.split(',')
        for predicate in predicates:
            if not re.match(r"^(([a-zA-Z¬])/)*([a-zA-Z¬])$", predicate.strip()):
                return False, "Invalid output predicates. Only literals, their negation and disjunction '/' are allowed. '/' must be preceded and followed by at least one literal or its negation."

    return True, ""

def generate_diagram(subject, in_predicates, out_predicates):
    fig, ax = plt.subplots()
    
    # Borra todos los "?" de la cadena entrante IN.
    out_predicates = out_predicates.replace('?', '')
    
    marlo_diagram = {
        'sub': subject,
        'in': in_predicates.split(','),
        # Condicional "if": Añade "?" siempre que contenga algo.  
        'out': [predicate + '?' if not predicate == "" else predicate for predicate in out_predicates.split(',')]
    }
    #if(predicate.find("?") == -1): 
    display_marlo(ax, marlo_diagram, '', '')

    plt.savefig('static/diagram.png', bbox_inches='tight')
    plt.close(fig)


def generate_predicates(subject, in_predicates, out_predicates):
    
    IN = in_predicates.split(',')
    OUT = out_predicates.split(',')

    formulas = []
    
    def generate_predicate_affirmative_subject(s):
        results = []
        
        if '?' not in s:
            s = s.replace('/', ' ⋁ ')
            s = '(' + s + ')'
            results.append(f"∃x({s.replace('/', ' ⋁ ')})")
        return results

    def generate_predicate_affirmative(s, in_list):
        results = []
        for in_item in in_list:
            if '?' not in in_item:
                in_item = in_item.replace('/', ' ⋁ ')
                in_item = '(' + in_item + ')'
                results.append(f"∃x(({s.replace('/', ' ⋁ ')}) ⋀ {in_item})")
        return results

    def generate_predicate_negative_from_Subject(s, in_list):
        if "?" not in in_list:
            in_predicates_str = ' ⋀ '.join([f"¬({predicate.replace('/', ' ⋁ ')})" for predicate in in_list])
            return [f"¬∃x (({s.replace('/', ' ⋁ ')}) ⋀ ({in_predicates_str}))"]
        return []
    
    def get_literals_from_predicates(predicates):
        literals = []
        for predicate in predicates:
            if predicate != "?":
                split_predicates = re.split(r'[/]', predicate)
                for literal in split_predicates:
                    split_literals = re.findall(r'[¬]?[a-zA-Z]', literal)
                    literals.extend(split_literals)
        return literals

    def generate_negative_predicates_from_IN(IN, OUT, subject):
        in_literals = get_literals_from_predicates(IN)
        out_literals = get_literals_from_predicates(OUT)
        literals_to_negate = list(set(in_literals) - set(out_literals))
        
        return [f"¬∃x({literal} ⋀ ¬({subject.replace('/', ' ⋁ ')}))" for literal in literals_to_negate]
    
    def generate_all_function(IN, subject):
        if any("/" in predicate for predicate in IN):
            return []
        in_literals = [literal for literals in IN for literal in literals.split('/') if literal != '?']
        in_literals = get_literals_from_predicates(in_literals)
        literal_counts = Counter(in_literals)
        all_literals = [literal for literal, count in literal_counts.items() if count == len(IN)]
        return [f"¬∃x(({subject.replace('/', ' ⋁ ')}) ⋀ ¬({literal})) -> generate_all_function" for literal in all_literals]

    def generate_conjunction_negation_in_OUT(OUT, subject):
        results = []
        for out_item in OUT:
            if '/' in out_item:
                literals = out_item.split('/')
                results.append(f"¬∃x(¬({subject.replace('/', ' ⋁ ')}) ⋀ ({' ⋀ '.join(literals)}))")
        return results
    
    def generate_only_exists_subject(IN, OUT, subject):
        
        in_literals = get_literals_from_predicates(IN)
        out_literals = get_literals_from_predicates(OUT)
    
        literals_to_check = list(set(in_literals) - set(out_literals))
        
        for literal in in_literals:
            if ('¬' + literal) in literals_to_check and literal in literals_to_check:
                return [f"¬∃x ¬({subject.replace('/', ' ⋁ ')})"]
    
        return []

    def generate_no_exists_subject(in_list, s):
        
        in_literals = get_literals_from_predicates(in_list)
        sujeto_literals = get_literals_from_predicates([s])

        in_predicates_str = ','.join(in_list)
        sujeto = ''.join(s)
        
        if re.search(r"(?<!⋁)([a-zA-Z¬])¬\1(?!⋁)", in_predicates_str) or re.search(r"(?<!⋁)([a-zA-Z¬])¬\1(?!⋁)", sujeto):
            return ["¬∃x(" + s + ")"]
        else:
            for literal in in_literals:
                for sujeto_literal in sujeto_literals:
                     if (('¬' + sujeto_literal) in in_literals and not any("/" in predicate for predicate in in_list) and not any("/" in predicate for predicate in s)) or (('¬' + literal) in sujeto_literals and not any("/" in predicate for predicate in in_list) and not any("/" in predicate for predicate in s)) :
                            return ["¬∃x(" + s + ")"]

        return []
       
    def disjunctive_syllogism(in_predicates, out_predicates):
        
        if any("/" in predicate for predicate in in_predicates):
            return []
        
        # Convertir las listas de predicados en listas de literales
        in_literals = get_literals_from_predicates(in_predicates)
        out_literals = get_literals_from_predicates(out_predicates)
        valid_formulas = set()  # Lista para almacenar todas las fórmulas válidas
        # Iterar sobre los literales en las regiones IN
        for literal_in_1 in in_literals:
            # Verificar que el literal está en todas las regiones IN
            if all(literal_in_1 in predicate for predicate in in_predicates):
                # Iterar de nuevo para encontrar el segundo literal
                for literal_in_2 in in_literals:
                    # Saltar si los literales son iguales
                    if literal_in_1 == literal_in_2:
                        continue
                    # Verificar que el segundo literal no está en ninguna región OUT
                    if all(literal_in_2 not in out_literal for out_literal in out_literals):
                        # Generar la fórmula deseada ¬∃x(P ⋀ ¬(Q)), donde P es ¬Q
                        new_formula = "¬∃x({} ⋀ ¬({})) -> disjunctive_syllogism".format(literal_in_2, literal_in_1)
                        valid_formulas.add(new_formula)
        # Si no se encuentra ninguna fórmula válida, devolver None
        if not valid_formulas:
            return ()
        # Si se encontraron fórmulas válidas, devolver la lista de fórmulas
        return valid_formulas

    formulas.extend(generate_predicate_affirmative_subject(subject))
    formulas.extend(generate_predicate_affirmative(subject, IN))
    formulas.extend(generate_predicate_negative_from_Subject(subject, IN))
    formulas.extend(generate_negative_predicates_from_IN(IN, OUT, subject))
    formulas.extend(generate_all_function(IN, subject))
    formulas.extend(disjunctive_syllogism(IN,OUT))
    formulas.extend(generate_conjunction_negation_in_OUT(OUT, subject))
    formulas.extend(generate_only_exists_subject(IN, OUT, subject))
    
    if generate_no_exists_subject(IN, subject) != []:
        formulas = generate_no_exists_subject(IN, subject)

    return formulas

def diag_text_view(md, textD, numD):
    return md

def display_marlo(ax, md, numD, textD, theColor='black'):
    LenIn = len(md['in'])
    if 'out' in md and len(md['out']) > 0:
        if LenIn < 3:
            display_marlo2(ax, md, numD, textD, theColor)
        elif LenIn == 3:
            display_marlo3(ax, md, numD, textD, theColor)
        elif LenIn == 4:
            display_marlo4(ax, md, numD, textD, theColor)
        else:
            ax.text(-0.7, 0.7, diag_text_view(md, textD, numD), fontsize=20, ha='left', va='top', color=theColor)
            ax.set_xlim(-1.1, 1.1)
            ax.set_ylim(-1, 1)
            ax.axis('off')
    else:
        ax.text(-0.7, 0.7, diag_text_view(md, textD, numD), fontsize=20, ha='left', va='top', color=theColor)
        ax.set_xlim(-1.1, 1.1)
        ax.set_ylim(-1, 1)
        ax.axis('off')

        if 'out' in md and len(md['out']) > 0:
            out_predicates = ['{}?'.format(predicate) for predicate in md['out']]
            if len(md['out']) > 0:
                ax.text(0.4, 0.9, out_predicates[0], fontsize=20, ha='center', va='center', color=theColor)
            if len(md['out']) > 1:
                ax.text(0.5, 0.7, out_predicates[1], fontsize=20, ha='center', va='center', color=theColor)
            if len(md['out']) > 2:
                ax.text(0.6, 0.5, out_predicates[2], fontsize=20, ha='center', va='center', color=theColor)
            if len(md['out']) > 3:
                ax.text(0.55, 0.3, "?".join(out_predicates[3:]), fontsize=20, ha='left', va='center', color=theColor)


def display_marlo2(ax, md, numberDia, textDia, theColor='black'):
    ellipse = patches.Ellipse((0, 0), 1, 2, edgecolor=theColor, facecolor='none', linewidth=3)
    ax.add_patch(ellipse)

    # Dibujar líneas
    if len(md['in']) > 1:
        ax.plot([-0.5, -0.15], [0, 0], color=theColor, linewidth=3)
        ax.plot([0.5, 0.15], [0, 0], color=theColor, linewidth=3)

    # Dibujar texto
    ax.text(0, -1.2, numberDia, fontsize=20, ha='center', va='center', color=theColor)
    ax.text(0, -1.4, textDia, fontsize=20, ha='center', va='center', color=theColor)

    ax.text(0, 0, md['sub'], fontsize=20, ha='center', va='center', color=theColor)
    innText = md['in'][-1]
    ax.text(0, -0.7, "".join(innText), fontsize=20, ha='center', va='center', color=theColor)
    if len(md['in']) > 1:
        innText = md['in'][0]
        ax.text(0, 0.7, "".join(innText), fontsize=20, ha='center', va='center', color=theColor)

    if len(md['out']) > 0:
        ax.text(0.4, 0.9, md['out'][0], fontsize=20, ha='center', va='center', color=theColor)
    if len(md['out']) > 1:
        ax.text(0.5, 0.7, md['out'][1], fontsize=20, ha='center', va='center', color=theColor)
    if len(md['out']) > 2:
        ax.text(0.6, 0.5, md['out'][2], fontsize=20, ha='center', va='center', color=theColor)
    if len(md['out']) > 3:
        ax.text(0.55, 0.3, "?".join(md['out'][3:]), fontsize=20, ha='left', va='center', color=theColor)

    # Ajustar los límites de la gráfica
    ax.set_xlim(-1, 1)
    ax.set_ylim(-1.1, 1.1)
    # Ocultar los ejes
    ax.axis('off')

def display_marlo3(ax, md, numberDia, textDia, theColor='black'):
    triangle = plt.Polygon(([-0.6, -1], [0.6, -1], [0, 0.6 * np.sqrt(3)]), fill=None,
                           edgecolor=theColor, linewidth=3)
    ax.add_patch(triangle)

    # Dibujar texto
    ax.text(0, -1.2, numberDia, fontsize=20, ha='center', va='center', color=theColor)
    ax.text(0, -1.4, textDia, fontsize=20, ha='center', va='center', color=theColor)

    ax.text(0, -0.2, md['sub'], fontsize=20, ha='center', va='center', color=theColor)
    innText = md['in'][0]
    if innText == []:
        innText = ['']
    ax.text(0.22, 0, "".join(innText), fontsize=20, ha='center', va='center',
            rotation=-60, color=theColor)
    innText = md['in'][1]
    if innText == []:
        innText = ['']
    ax.text(-0.25, 0, "".join(innText), fontsize=20, ha='center', va='center',
            rotation=60, color=theColor)
    innText = md['in'][2]
    if innText == []:
        innText = ['?']
    ax.text(0, -0.85, "".join(innText), fontsize=20, ha='center', va='center',
            color=theColor)
    if len(md['out']) > 0:
        ax.text(0.15, 0.9, md['out'][0] + "", fontsize=20, ha='center', va='center', color=theColor)
    if len(md['out']) > 1:
        ax.text(0.2, 0.7, md['out'][1] + "", fontsize=20, ha='center', va='center', color=theColor)
    if len(md['out']) > 2:
        ax.text(0.25, 0.5, md['out'][2] + "", fontsize=20, ha='center', va='center', color=theColor)
    if len(md['out']) > 3:
        ax.text(0.25, 0.3, "?".join(md['out'][3:]) + "", fontsize=20, ha='left', va='center', color=theColor)
    # Ajustar los límites de la gráfica
    ax.set_xlim(-0.7, 0.7)
    ax.set_ylim(-1.1, 1.1)
    # Ocultar los ejes
    ax.axis('off')

def display_marlo4(ax, md, numberDia, textDia, theColor='black'):
    square = plt.Polygon(([-0.8, -0.9], [0.8, -0.9], [0.8, 1], [-0.8, 1]), fill=None,
                         edgecolor=theColor, linewidth=3)
    ax.add_patch(square)

    # Dibujar texto
    ax.text(0, -1.2, numberDia, fontsize=20, ha='center', va='center', color=theColor)
    ax.text(0, -1.4, textDia, fontsize=20, ha='center', va='center', color=theColor)

    ax.text(0, 0, md['sub'], fontsize=20, ha='center', va='center', color=theColor)
    innText = md['in'][0]
    if innText == []:
        innText = ['?']
    ax.text(0.7, 0, "".join(innText), fontsize=20, ha='center', va='center',
            rotation=-90, color=theColor)
    innText = md['in'][1]
    if innText == []:
        innText = ['?']
    ax.text(0, 0.9, "".join(innText), fontsize=20, ha='center', va='center',
            rotation=0, color=theColor)
    innText = md['in'][2]
    if innText == []:
        innText = ['?']
    ax.text(-0.7, 0, "".join(innText), fontsize=20, ha='center', va='center',
            rotation=90, color=theColor)
    innText = md['in'][3]
    if innText == []:
        innText = ['?']
    ax.text(0, -0.8, "".join(innText), fontsize=20, ha='center', va='center',
            rotation=0, color=theColor)

    if len(md['out']) > 0:
        ax.text(0.9, 0.9, md['out'][0] + "", fontsize=20, ha='left', va='center', color=theColor)
    if len(md['out']) > 1:
        ax.text(0.9, 0.7, md['out'][1] + "", fontsize=20, ha='left', va='center', color=theColor)
    if len(md['out']) > 2:
        ax.text(0.9, 0.5, md['out'][2] + "", fontsize=20, ha='left', va='center', color=theColor)
    if len(md['out']) > 3:
        ax.text(0.9, 0.3, "?".join(md['out'][3:]) + "", fontsize=20, ha='left', va='center', color=theColor)
    ax.set_xlim(-1.1, 1.1)
    ax.set_ylim(-1.1, 1)
    ax.axis('off')

@app.route('/', methods=['GET', 'POST'])
def create_diagram():
    if request.method == 'POST':
        subject = request.form['subject']
        in_predicates = request.form['in_predicates']
        out_predicates = request.form['out_predicates']
        
        valid_input, error_message = validate_input(subject, in_predicates, out_predicates)
        if not valid_input:
            return render_template('index.html', error=error_message)
        
        generate_diagram(subject, in_predicates, out_predicates)
        
        predicates = generate_predicates(subject, in_predicates, out_predicates)
        
        return render_template('index.html', diagram_image=True, predicates=predicates)

    return render_template('index.html')

if __name__ == '__main__':
    app.run(debug=True)
